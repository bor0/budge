# Budge-TP — Claude working notes

Keep this file compact: short statements, no repetition. Merge new notes into existing
sections rather than appending, and don't drop information when trimming.

## Running

```
python3 budge-tp.py examples/<file>.btp
# all examples must pass after any change:
for f in examples/*.btp examples/lib/*.btp; do python3 budge-tp.py "$f" 2>&1 | grep -q "Traceback" && echo "FAIL: $f"; done
# --expand DIR writes every loaded file with <?py ... ?> blocks replaced by their output
```

## Syntax

```
r<name> : <expr> [-> <expr> ...]               # rule; last expr is the conclusion
t<name> : <rule> [x=T1;y=T2;...] [hyp1] ...    # theorem
p<name> : <text>                               # prose, printed as `-- <text>` in source order
<?py ... ?>                                    # Python meta-program; emits Budge code
```

- Single lowercase letters in rules are variables; `x=T` replaces `x` with theorem `T`'s *value*.
- Hypotheses are theorems whose values must equal the rule's substituted hypotheses.
- Trailing `!` suppresses output (theorems, prose); the `-- ` prefix stops prose spoofing a theorem.
- `#` starts a comment anywhere.
- Python blocks: `<?py` and `?>` on their own lines, or one line `<?py code ?>`; run with
  `__file__`, `env` (all read and checked so far) and `load(path)`; what they print is spliced
  in and checked. That's all budge-tp.py does. There is no import statement.
- `<?py load('lib/x.btp') ?>`: path relative to this file; fully checked, shares one namespace
  (clashes are errors), loads once (diamonds fine, cycles are errors), prints nothing.
  `--expand` keeps these lines and replaces every other block.
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

**Predicates in rules.** A rule like `rInd : ⊢p(0) -> … -> ⊢∀X,p(X)` substitutes `p`
literally: `p=EQ(ADD(0,x),x)` gives `EQ(ADD(0,x),x)(0)` (no beta-reduction). Old fix: a
defined predicate (`⊢(BODY(x)=>PRED(x))`, `⊢(PRED(x)=>BODY(x))`, pass `p=tmPRED!`). Better:
de Bruijn bodies with OPEN, as in `lib/peano.btp`'s `rInd` (below).

**Inductive step, Hilbert-style.** No hypothetical reasoning: meta rules like
`⊢EQ(x,y) -> ⊢EQ(S(x),S(y))` only fire on proved facts, so can't build
`⊢(PRED(n)=>PRED(S(n)))`. By the deduction theorem, state facts as object-level
implications (`⊢(EQ(x,y)=>EQ(S(x),S(y)))`, curried `rEqT : ⊢(EQ(x,y)=>(EQ(y,z)=>EQ(x,z)))`),
chain with `rMp` and hypothetical syllogism (`thHS` in `lib/logic.btp`). An unconditional
fact (`⊢H` from `rAS`) feeds a curried implication via `rMp`, leaving `⊢(F=>G)` to chain. Never axiomatise the step
(`rImpl : ⊢(PRED(n)=>PRED(S(n)))`): that assumes the proof's content.

**Induction variable must stay arbitrary.** With a schematic `n` step
(`rInd : ⊢p(0) -> ⊢(p(n)=>p(S(n))) -> …`), passing `n=tmZ!` checks the step only at 0 and
Budge can't tell. `lib/peano.btp` avoids this: the step is about parameter `N`, and the
premise `ABS(0,N,g,f)` checks N is not in the formula.

**Tally numbers** (`lib/tally.btp`, `rsa.btp`). `|||` = 3; template `zx` concatenates, so adding is free:
```
rMulSucc : x*y=z MOD n -> x*y|=zx MOD n   # x*(y+1) = x*y + x, one step
rMulRed  : x*y=zn MOD n -> x*y=z MOD n    # subtract n in one step
```
No zero (values can't be empty): pick inputs with no 0 intermediates. `rMulRed` proves
congruence, not full reduction.

**Hoare assignment** (`hoare.btp`, rules in `lib/hoare.btp`). `{Q[e/x]} x:=e {Q}` can't be
generic (no substitution inside values); `{q} x:=e {p}` is unsound (accepts any
precondition). Fix the assertion shape, one axiom per program variable (side conditions
unchecked), so Q[e/x] is just filling in `e`; they stay in the program's file:
```
rAssignI : {EQ(a,DIV2(e))} $I = e; {EQ(a,DIV2($I))}   # a must not mention $I
rAssignS : {EQ(e,g)} $S = e; {EQ($S,g)}               # g must not mention $S
```
Keep assertions in shape by ordering: the increment comes *after* the `IF`, so stepping
back over `$I = S($I)` gives `EQ($S,DIV2(S($I)))`. Program text and conditions use library
notation (`EQ`, `¬`, `MOD2`), so `rIf`/`rWhile` put conditions into assertions as is, and
the verification conditions are library lemmas (`lib/parity.btp`), not axioms.

**Quantifiers** (`lib/fol.btp`). `rInst` can't handle nesting or capture; use de
Bruijn indices: `ALL(EX(R(V(S(0)),V(0))))` is ∀x∃y R(x,y). Two judgements, one
structural rule per constructor (a new symbol needs both, plus CT for function symbols):
- `OPEN(k,f,t,g)`: g is f with `V(k)` replaced by closed t →
  `rAllE : OPEN(0,f,t,g) -> ⊢(ALL(f)=>g)`, `rExI` (∃ intro, same OPEN).
- `ABS(k,w,g,f)`: f is g with every parameter `w` replaced by `V(k)` (no `ABS(k,w,w,w)`,
  so none left; other parameters pass via `DIFF(w,o)`) → `rGen : ABS(0,w,g,f) -> ⊢g -> ⊢ALL(f)`.
- `rExE` and `rAllImp` need q closed: `OPEN(0,q,K,q)` (opening changes nothing).
Both accept only `V(n)` with `LT(n,k)` (sentences): no shifting, no capture. Unchecked:
parameters (K < M < N < U < W < X < Y < Z, distinct via the `PLT` order) must not occur in
non-logical axioms.

**Library** (`examples/lib/`). `logic.btp`: K, S, `rNeg`, ∧, ∨, ⊤, MP; exports `thId`, `thHS`,
`thMpI`, `thDNE`, `thDNI`, `thCP`, `thAndComm`, `thOrComm`, `thEFQ`, `thDS` (proofs in a, b, c,
exported in i, j, l; internal steps prefixed `thLg…`). Examples load it with
`<?py load('lib/logic.btp') ?>` and reuse it, never redefine it in any notation.
`fol.btp` (loads logic): V, ALL, EX, EQ with `rEqR`/`rEqS`/`rEqT`, the judgements above,
`rAllE`/`rExI`/`rGen`/`rExE`/`rAllImp`, numerals 0 and S; exports `tm0!`…`tm4!`, `tmV0!`,
`tmV1!`, `tmK!`…`tmZ!`, `thLt01!`, `thParK!`…, `thCt0!`, `thCtM!`, `thAbsM!`. A file adding a
symbol declares its term/CT/OPEN/ABS(/congruence) rules (`quantifiers.btp`: A, P, Q, R).
`peano.btp` (loads fol): S never 0 and injective, + and × by recursion, congruence for S,
ADD, MUL, their CT/OPEN/ABS, and induction `rInd`; numbers are fol's numerals.
`list.btp` (loads fol, for numbers `S(x)` and LT): pairs, NIL, TRUE/FALSE, APPEND, CAR/CDR,
MEMBER, SUM, MAX, substitution, REV, SORTED; exports `tmNil!`, `tmT!`, `tmF!`.
`boolean.btp` (loads fol): Huntington's axioms over fol's terms (∧, ∨, ¬, 0, 1), with ∧/∨
congruence and the syntax rules for 1. Equality is fol's: a meta-level `⊢EQ(x,y) -> ⊢EQ(y,x)`
in an example would duplicate `rEqS`.
`strings.btp` (loads nothing): concatenation `xy`, sequences `x y`, GEB's hyphen strings
(`tm-!`…`tm----!`). Same text with a different meaning (`0` as a bit, `K` as a combinator) is
not a duplicate: don't load a library for a coincidental symbol.
`tally.btp` (loads strings): bar tallies `|||`, ≤, multiplication and powers MOD n; exports
`tmBar1!`…`tmBar10!`. Cheap arithmetic for computations; proofs about all numbers use peano.
`semiring.btp` (loads peano; Python block): `thZeroAdd` … `thMulAssoc`, all closed ∀ sentences
(0+n = n, S(m)+n = S(m+n), + and · commutative and associative, distributivity, …).
`sum.btp` (loads peano): SUM(n) = 0+1+…+n by recursion; `gauss.btp` proves 2·SUM(n) = n·S(n).
`parity.btp` (loads peano; Python block): FLIP, MOD2, DIV2 by recursion; `thModDich`,
`thDiv2Odd`, `thDiv2Even`. `hoare.btp` (loads logic, strings): Hoare rules and program syntax.

Big proofs are `<?py ... ?>` blocks over `examples/lib/tactics.py`. A block starts
`import os, sys; sys.path.insert(0, <dir of examples/lib>)`, `from tactics import *`,
`use(env, __file__)`; `use` loads everything checked above it, and terms and judgements are
reused by value, so printed names never clash. Numbered terms are `tm<Tag><n>!`, the tag
from the file name (+`L` in `lib/`). Loaded files share one namespace, so a library's
internal names must be distinctive (`thPtA1!`, not `thA1!`). tactics.py grows with the
library: it holds only what the committed proofs use.

**Induction with de Bruijn ∀** (`lib/peano.btp`). No defined predicates:
`rInd : OPEN(0,f,0,b) -> ABS(0,N,g,f) -> OPEN(0,f,S(N),h) -> ⊢b -> ⊢(g=>h) -> ⊢ALL(f)`;
the ABS premise also checks N ∉ f. Several parameters: `ABS(k,w,g,f)` names the
parameter `w` (`PAR(w)`), others pass via `DIFF(w,o)`. Use the IH as `thId` `⊢(G=>G)`;
steps under G: `rK` weakens facts, `thHS` chains, `rS` + `rEqT` give transitivity.

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
