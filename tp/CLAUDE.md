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

### Defined predicates for induction

`rInd : ⊢p(0) -> ⊢(p(n)=>p(S(n))) -> ⊢∀X,p(X)` substitutes `p` literally.
So `p=EQ(ADD(0,x),x)` gives `p(0)` → `EQ(ADD(0,x),x)(0)` (wrong).

Fix: introduce a named predicate `PRED` by definition — two axioms
`rPREDI : ⊢(BODY(x)=>PRED(x))` and `rPREDE : ⊢(PRED(x)=>BODY(x))`, i.e.
`PRED(x) <=> BODY(x)` — and pass the bare name: `p=tmPRED!`. This is a
definitional extension (conservative), not a workaround.

See `zero_plus_n_induction.btp` for the full pattern.

### Proving the inductive step (Hilbert-style)

Budge has no hypothetical reasoning ("assume A, derive B, conclude A=>B"), so
the step `⊢(PRED(n)=>PRED(S(n)))` can't be built from meta-level rules like
`⊢EQ(x,y) -> ⊢EQ(S(x),S(y))` — those only fire on already-proved facts.
Instead, by the deduction theorem, prove it Hilbert-style:

- state the facts used under the assumption as object-level implications
  (`rCongS : ⊢(EQ(x,y)=>EQ(S(x),S(y)))`, curried `rEqT : ⊢(EQ(x,y)=>(EQ(y,z)=>EQ(x,z)))`)
- chain them with `rMp` and hypothetical syllogism `⊢((b=>c)=>((a=>b)=>(a=>c)))`,
  derived from axioms K and S as in `hilbert.btp`
- an unconditional fact (e.g. `⊢H` from `rAS`) feeds into a curried implication
  via `rMp`, leaving `⊢(F=>G)` to chain

Do **not** axiomatise the step itself (`rImpl : ⊢PRED(n)=>PRED(S(n))`) — that
assumes the content of the proof.

### Schematic inductive step (important)

When applying `rInd`, do **not** fix `n` to a specific value. Leave it schematic:

```
# Wrong — inductive step only verified at n=0:
thStep! : ... built with n=tmZ! ...
thResult : rInd p=tmP!;n=tmZ! thBase! thStep!

# Correct — inductive step is schematic for any n:
rTmN : n
tmN! : rTmN                 # use x=tmN! wherever a rule needs n
thResult : rInd p=tmP! thBase! thStep!
```

This works because the rule's `(p(n)=>p(S(n)))` after substituting only `p`
becomes `(PRED(n)=>PRED(S(n)))`, which matches a step proved with literal `n`.
Budge does **not** check this side condition; soundness relies on the convention.
Never use `n` as a substitution key in such files, since values contain it.

### Object-level implications and modus ponens

Use `rMp : ⊢p -> ⊢(p=>q) -> ⊢q` and write **every** implication fully
parenthesised, `(A=>B)`, in axioms and in terms built via `rTmImp : (p=>q)`.
Matching is exact string equality, so mixing `A=>B` and `(A=>B)` breaks proofs.

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
Add one general rule, `rInst : ⊢∀X,p(X) -> ⊢p(x)`, and apply it with
`p=tmPRED!;x=...` (works because `p` is a bare predicate name).

### Quantifiers with binding (de Bruijn)

`rInst` above substitutes a bare predicate name and can't deal with nested
quantifiers or capture. For real first-order binding, see `quantifiers.btp`:
bound variables are de Bruijn indices (`ALL(EX(R(V(S(Z)),V(Z))))` is
∀x∃y R(x,y)), and binding is handled by two derived judgements, built with one
structural rule per constructor:

- `OPEN(k,f,t,g)` — g is f with `V(k)` (at depth k) replaced by closed term t.
  Feeds `rAllE : OPEN(Z,f,t,g) -> ⊢IMP(ALL(f),g)` and `rExI` (∃ intro).
- `ABS(k,g,f)` — f is g with every parameter `X` replaced by `V(k)`. There is
  no `ABS(k,X,X)`, so no X is left behind. Feeds `rGen : ABS(Z,g,f) -> ⊢g -> ⊢ALL(f)`.
  `ABS(Z,q,q)` doubles as a "q is closed" check for ∃E.

Both rules only accept `V(n)` with `LT(n,k)`, i.e. sentences, so no index
shifting is needed and closed terms can't be captured. Side condition (not
checked): the eigenvariable `X` must not occur in non-logical axioms.
Adding a constructor means adding its `OPEN` and `ABS` rules.

### Unbound conclusion variables

Every variable in a rule's conclusion should also appear in a hypothesis (or
be deliberately free, as in a term rule or axiom schema). A variable bound
only by the conclusion can be given any value through `x=T`, and a hypothesis
missing a field never matches a real state. Budge doesn't flag either, and a
rule no theorem uses is never exercised. Example: `coordgame.btp`'s
`rCoordW` once read `P(x,S(y)) E(a,b) -> P(x,y) E(a,b) HP=h`, dropping
`HP=h` from its hypothesis, and went unnoticed because no theorem used it.

### Where the answer lives: theorem vs proof

Relation-style files (`list.btp`: `APPEND(a, b, c)`) keep inputs and outputs
in the theorem. State-machine files (`rle.btp`, `hanoi.btp`) don't: the final
`CODED=… DECODED=NIL` says nothing about which input it encodes, and Hanoi's
move sequence exists only in the proof. To make "f(input) = output" a
theorem, carry the input through every state (`INPUT=i ...`) to a final
`ENCODE(i)=y`. A `.btp` file holds only logic: which argument is the output,
and whether to search forward or backward, isn't recorded anywhere
(Kowalski's "Algorithm = Logic + Control").

## Known limitations

- **No general unification** — matching is exact string equality after substitution
- **No backtracking or proof search** — theorems are evaluated strictly in source order
- **No lambda / beta-reduction** — predicates cannot be passed as higher-order arguments; use a defined predicate instead
- **No universal instantiation built in** — add a general `rInst` rule, or encode binding with de Bruijn indices (see above)
- **No hypothetical reasoning** — object-level implications can't come from meta-level rules; derive them Hilbert-style (see above)
- **No free-variable tracking** — the schematic-`n` side condition of `rInd` is a convention, not checked
- **Single lowercase letters only** as substitution variables

## Conventions used in examples

- `r<Name>` — inference rule or axiom
- `tm<Name>!` — suppressed term (used as argument to other theorems)
- `th<Name>!` — suppressed intermediate proof step
- `th<Name>` — final visible theorem
- Object-level variables: uppercase (`X`, `A`, `B`)
- Meta-level variables in rules: single lowercase letters (`p`, `q`, `x`, `y`, `m`, `n`)
- Section headings use single `#` comments
