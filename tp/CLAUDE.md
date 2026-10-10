# Budge-TP — Claude working notes

## Running

```
python3 budge-tp.py examples/<file>.btp
```

All examples must pass after any change:
```
for f in examples/*.btp; do python3 budge-tp.py "$f" 2>&1 | grep -q "Traceback" && echo "FAIL: $f"; done
```

## Language syntax

```
r<name> : <expr> [-> <expr> -> ... -> <expr>]  # rule
t<name> : <rule> [x=T1;y=T2;...] [hyp1] [hyp2] # theorem
p<name> : <text>                               # prose (printed as-is, in source order)
```

- `->` separates hypotheses from conclusion (last expression is the conclusion)
- Lowercase single letters in rule expressions are variables — substituted literally as strings
- `x=T` in a theorem replaces `x` in the rule with the *value* of theorem `T`
- Hypotheses (`hyp1 hyp2 ...`) are theorems whose values must match the rule's hypotheses after substitution
- Names ending in `!` are suppressed from output (applies to theorems and prose)
- Lines starting with `#` are comments (everything after `#` on any line is stripped)
- Prose statements print as `-- <text>` interleaved with theorem output in source order; the `-- ` prefix prevents prose from spoofing a theorem result

## How substitution works

Substitution is **pure string replacement** — no unification, no structure awareness.

Given rule `rFoo : ⊢p -> ⊢p=>q -> ⊢q` and theorem `tBar : rFoo p=tmA!;q=tmB! h1 h2`:
1. Resolve replacements: look up `tmA!` and `tmB!` in the theorem table, get their string values
2. Replace `p` and `q` in the rule's hypotheses and conclusion with those strings
3. Compare the substituted rule hypotheses against the values of `h1` and `h2`
4. If they match, return the substituted conclusion as the theorem's value

**Implication**: a variable like `p` in a rule gets replaced everywhere it appears as the literal character `p`. This means variable names must not appear as substrings of other terms (e.g., `p` must not appear inside `q`'s value if they're both substituted).

## Substitution mechanics (implementation detail)

Replacements are applied in the **order specified**, each via Python `.replace()` on the accumulated string. Because `.replace()` is case-sensitive, uppercase-only object-level term values are never touched by lowercase meta-variable substitutions — no cascading occurs. This is the reason the convention "uppercase for object-level" exists: it is a **correctness technique**, not just style.

## Hypotheses without substitutions

The parser unconditionally treats `arguments[1]` as the replacements field. If a rule has hypotheses but requires no substitution, use a bare `;` as a placeholder:

```
# Wrong — hyp gets parsed as a replacement string and errors:
tFoo : rBar hyp1

# Correct — semicolon produces an empty replacement dict:
tFoo : rBar ; hyp1
```

## Key patterns

### Hoare assignment: fixed-shape assertions

The assignment axiom `{Q[e/x]} x:=e {Q}` cannot be written generically:
substitution only happens in rule templates, never inside a value, so one
value can't yield both `Q` and `Q[e/x]`. (A rule like `{q} x:=e {p}` with
`p`, `q` supplied separately is unsound — it accepts any precondition.)

Workaround: fix the shape of assertions so the assigned variable sits in a
known slot, and give each program variable its own axiom:

```
rAssignI : {a == f(e, k)} $I = e; {a == f($I, k)}   # a, f, k must not mention $I
rAssignS : {e == g} $S = e; {$S == g}               # g must not mention $S
```

Under that shape, Q[e/x] is just filling `e` into the template. The side
conditions are not checked by Budge. Order the program so intermediate
assertions stay in shape: in `hoare.btp` the increment comes *after* the
`IF`, so stepping back over `$I = $I + 1` gives `$S == INTDIV($I + 1, 2)`,
which already fits — no helper predicates needed.

PHP keywords and function names are case-insensitive, so `WHILE`, `IF`,
`INTDIV` and `$I`/`$S` keep all program text uppercase and safe from
meta-variable substitution, while assertions stay valid PHP expressions.

### Term lifting

Rules produce string conclusions directly. To use a complex expression as a substitution value, define it as a term rule:

```
rTmFoo : Foo(x)         # term rule, conclusion is the term shape
tmFoo! : rTmFoo x=tmX!  # applies it, giving value Foo(X)
```

### Predicate wrapping for induction

`rInd : ⊢p(0) -> ⊢p(n)=>p(S(n)) -> ⊢∀X,p(X)` substitutes `p` literally.
So `p=EQ(ADD(0,x),x)` gives `p(0)` → `EQ(ADD(0,x),x)(0)` (wrong).

Fix: wrap the predicate as a named symbol `PRED`, define intro/elim rules, use `p=tmPRED!`.

See `zero_plus_n_induction.btp` for the full pattern.

### Schematic inductive step (important)

When applying `rInd`, do **not** fix `n` to a specific value. Leave it schematic:

```
# Wrong — inductive step only verified at n=0:
thStep! : rMyImpl n=tmZ!
thResult : rInd p=tmP!;n=tmZ! thBase! thStep!

# Correct — inductive step is schematic for any n:
thStep!  : rMyImpl          # n stays as literal 'n'
thResult : rInd p=tmP! thBase! thStep!
```

This works because the rule's `p(n)=>p(S(n))` after substituting only `p` becomes `PRED(n)=>PRED(S(n))`, which matches an unsubstituted `rMyImpl` conclusion.

### Object-level modus ponens

Add `rMp : ⊢p -> ⊢p=>q -> ⊢q` when you need to fire object-level implications.
Note: **no outer parentheses** around `p=>q` in the template, because `rZPEQImpl`-style rules produce `⊢A=>B` without them. (Contrast with `hilbert.btp`'s `rMp : ⊢p -> ⊢(p=>q) -> ⊢q`, which works there because all `tm...!` terms are built with explicit parens via `rTmImp`.)

### Tally numbers (free addition)

Peano `SS0` needs one step per unit to add. Tallies (`|||` = 3) make addition
free: the rule template `zx` concatenates the values, so it *is* z+x.

```
rMulSucc : x*y=z MOD n -> x*y|=zx MOD n   # x*(y+1) = x*y + x, one step
rMulRed  : x*y=zn MOD n -> x*y=z MOD n    # subtract n in one step
```

Caveats: there is no zero (a term can't have an empty value), so pick inputs
whose intermediate results are never 0; and `rMulRed` only proves congruence,
not that the result is fully reduced below `n`. See `rsa.btp`.

### Instantiation from universals

`rInd` produces `⊢∀X,PRED(X)` but there is no built-in universal instantiation.
Add a predicate-specific rule: `rInstPRED : ⊢∀X,PRED(X) -> ⊢PRED(x)`.
Then derive concrete instances by applying it to the universal theorem.

## Known limitations

- **No general unification** — matching is exact string equality after substitution
- **No backtracking or proof search** — theorems are evaluated strictly in source order
- **No lambda / beta-reduction** — predicates cannot be passed as higher-order arguments; use the wrapper pattern instead
- **No universal instantiation built in** — must add per-predicate instantiation rules
- **Object-level implications cannot be derived** from meta-level hypothetical reasoning; they must be axiomatised (`rImpl : ⊢A=>B`) and the comment should note why it's justified
- **Single lowercase letters only** as substitution variables

## Conventions used in examples

- `r<Name>` — inference rule or axiom
- `tm<Name>!` — suppressed term (used as argument to other theorems)
- `th<Name>!` — suppressed intermediate proof step
- `th<Name>` — final visible theorem
- Object-level variables: uppercase (`X`, `A`, `B`)
- Meta-level variables in rules: single lowercase letters (`p`, `q`, `x`, `y`, `m`, `n`)
- Section headings use single `#` comments
