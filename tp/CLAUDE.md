# Budge-TP — Claude working notes

Keep this file compact: short statements, no repetition. Merge new notes into existing
sections rather than appending, and don't drop information when trimming.

## Running

```
python3 budge-tp.py examples/<file>.btp
# all examples must pass after any change:
for f in examples/*.btp; do python3 budge-tp.py "$f" 2>&1 | grep -q "Traceback" && echo "FAIL: $f"; done
```

## Syntax

```
r<name> : <expr> [-> <expr> ...]               # rule; last expr is the conclusion
t<name> : <rule> [x=T1;y=T2;...] [hyp1] ...    # theorem
p<name> : <text>                               # prose, printed as `-- <text>` in source order
```

- Single lowercase letters in rules are variables; `x=T` replaces `x` with theorem `T`'s *value*.
- Hypotheses are theorems whose values must equal the rule's substituted hypotheses.
- Trailing `!` suppresses output (theorems, prose); the `-- ` prefix stops prose spoofing a theorem.
- `#` starts a comment anywhere.
- Field 2 is always parsed as replacements, so hypotheses without substitutions need a
  bare `;`: `tFoo : rBar ; hyp1`, not `tFoo : rBar hyp1`.

## Substitution

For `tBar : rFoo p=tmA!;q=tmB! h1 h2`: take the values of `tmA!`/`tmB!`, apply each
in order with Python `.replace()` to the rule's hypotheses and conclusion, require the
hypotheses to equal `h1`/`h2`'s values exactly, return the conclusion. No unification,
structure or proof search; theorems are checked in source order. A variable is
replaced *everywhere*, so it must not occur inside other values — hence uppercase
object-level terms: a correctness technique (lowercase replacements can't touch them).

## Patterns

**Term lifting.** Complex values come from term rules: `rTmFoo : Foo(x)`, `tmFoo! : rTmFoo x=tmX!`.

**Implications.** `rMp : ⊢p -> ⊢(p=>q) -> ⊢q`; always parenthesise `(A=>B)` — mixing
with `A=>B` breaks matching.

**Defined predicates** (`zero_plus_n_induction.btp`). `rInd : ⊢p(0) -> ⊢(p(n)=>p(S(n))) -> ⊢∀X,p(X)`
substitutes `p` literally: `p=EQ(ADD(0,x),x)` gives `EQ(ADD(0,x),x)(0)`. No lambda or
beta-reduction, so instead define `PRED(x) <=> BODY(x)` by axioms `⊢(BODY(x)=>PRED(x))`,
`⊢(PRED(x)=>BODY(x))` (conservative) and pass `p=tmPRED!`. Instantiate with a general
`rInst : ⊢∀X,p(X) -> ⊢p(x)`, `p=tmPRED!;x=…` (works since `p` is a bare name).

**Inductive step, Hilbert-style.** No hypothetical reasoning: meta rules like
`⊢EQ(x,y) -> ⊢EQ(S(x),S(y))` only fire on proved facts, so can't build
`⊢(PRED(n)=>PRED(S(n)))`. By the deduction theorem, state facts as object-level
implications (`⊢(EQ(x,y)=>EQ(S(x),S(y)))`, curried `rEqT : ⊢(EQ(x,y)=>(EQ(y,z)=>EQ(x,z)))`),
chain with `rMp` and hypothetical syllogism `⊢((b=>c)=>((a=>b)=>(a=>c)))` (from K, S;
see `hilbert.btp`). An unconditional fact (`⊢H` from `rAS`) feeds a curried implication
via `rMp`, leaving `⊢(F=>G)` to chain. Never axiomatise the step
(`rImpl : ⊢(PRED(n)=>PRED(S(n)))`): that assumes the proof's content.

**Schematic `n`.** Prove the step with literal `n` (`rTmN : n`, `tmN! : rTmN`) and omit
`n=` when applying `rInd`; substituting only `p` gives `(PRED(n)=>PRED(S(n)))`, which
matches. Never use `n` as a substitution key there. Unchecked by Budge.
```
thResult : rInd p=tmP!;n=tmZ! thBase! thStep!   # wrong: step only checked at n=0
thResult : rInd p=tmP! thBase! thStep!          # right: step schematic in n
```

**Tally numbers** (`rsa.btp`). `|||` = 3; template `zx` concatenates, so adding is free:
```
rMulSucc : x*y=z MOD n -> x*y|=zx MOD n   # x*(y+1) = x*y + x, one step
rMulRed  : x*y=zn MOD n -> x*y=z MOD n    # subtract n in one step
```
No zero (values can't be empty): pick inputs with no 0 intermediates. `rMulRed` proves
congruence, not full reduction.

**Hoare assignment** (`hoare.btp`). `{Q[e/x]} x:=e {Q}` can't be generic (no
substitution inside values); `{q} x:=e {p}` is unsound (accepts any precondition). Fix
the assertion shape, one axiom per program variable (side conditions unchecked), so
Q[e/x] is just filling in `e`:
```
rAssignI : {a == f(e, k)} $I = e; {a == f($I, k)}   # a, f, k must not mention $I
rAssignS : {e == g} $S = e; {$S == g}               # g must not mention $S
```
Keep assertions in shape by ordering: the increment comes *after* the `IF`, so stepping
back over `$I = $I + 1` gives `$S == INTDIV($I + 1, 2)` — no helper predicates. Program
text is uppercase (`WHILE`, `INTDIV`, `$I`): PHP keywords/functions are
case-insensitive, so it stays valid PHP yet safe from substitution.

**Quantifiers** (`quantifiers.btp`). `rInst` can't handle nesting or capture; use de
Bruijn indices: `ALL(EX(R(V(S(Z)),V(Z))))` is ∀x∃y R(x,y). Two judgements, one
structural rule per constructor (a new constructor needs both):
- `OPEN(k,f,t,g)`: g is f with `V(k)` replaced by closed t →
  `rAllE : OPEN(Z,f,t,g) -> ⊢IMP(ALL(f),g)`, `rExI` (∃ intro).
- `ABS(k,g,f)`: f is g with every parameter `X` replaced by `V(k)` (no `ABS(k,X,X)`, so
  none left) → `rGen : ABS(Z,g,f) -> ⊢g -> ⊢ALL(f)`; `ABS(Z,q,q)` = "q closed" for ∃E.

Both accept only `V(n)` with `LT(n,k)` (sentences): no shifting, no capture. Unchecked:
eigenvariable `X` must not occur in non-logical axioms.

## Pitfalls

- **Unbound conclusion variables.** One absent from every hypothesis can be set to
  anything via `x=T` (fine only for term rules/axiom schemas); a hypothesis missing a
  field never matches. Unused rules go unexercised: `coordgame.btp`'s `rCoordW` once
  dropped `HP=h` from its hypothesis unnoticed.
- **Theorem vs proof.** Relations (`list.btp`: `APPEND(a,b,c)`) keep input and output in
  the theorem; state machines (`rle.btp`, `hanoi.btp`) keep input/path only in the proof
  (rle's final `CODED=… DECODED=NIL` doesn't say what it encodes). For `ENCODE(i)=y` as a
  theorem, carry `INPUT=i` through every state. A `.btp` is logic only: output mode and
  search direction aren't recorded (Kowalski: "Algorithm = Logic + Control").

## Conventions

`r<Name>` rule/axiom · `tm<Name>!` suppressed term · `th<Name>!` intermediate step ·
`th<Name>` visible result · uppercase object-level (`X`, `A`) · single lowercase
meta-variables · section headings as `#` comments.
