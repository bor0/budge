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

`spacefast/index.html` is the browser playground; it fetches the checker and examples from
GitHub `main` at run time. Keep it in step with any change: `LIB` lists every `examples/lib/`
file, the `runEx` dropdown offers the showcase examples, the `TACS` cards match tactics.py's
names and behaviour, and the prose matches the code. It must stay phone-friendly (no horizontal
scroll at 320px). After changing it, republish it (spacefast skill) to its existing Space, https://budge.space.fast/ (linked from
README.md), updating it rather than creating one; that needs the owner's API key. No `.spacefast/` folder.

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

**Inductive step, Hilbert-style.** Budge has no open assumptions: meta rules like
`⊢EQ(x,y) -> ⊢EQ(S(x),S(y))` only fire on proved facts, so can't build
`⊢(PRED(n)=>PRED(S(n)))`. By the deduction theorem, state facts as object-level
implications (`⊢(EQ(x,y)=>EQ(S(x),S(y)))`, curried `rEqT : ⊢(EQ(x,y)=>(EQ(y,z)=>EQ(x,z)))`),
chain with `rMp` and hypothetical syllogism (`thHS` in `lib/logic.btp`). An unconditional
fact (`⊢H` from `rAS`) feeds a curried implication via `rMp`, leaving `⊢(F=>G)` to chain. Never axiomatise the step
(`rImpl : ⊢(PRED(n)=>PRED(S(n)))`): that assumes the proof's content. Python blocks
don't do this by hand: `Ctx` (below) compiles assume/discharge to these steps.

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

**Hoare assignment** (rules in `lib/hoare.btp`). General: `rAssign : ABS(0,x,q,f) ->
OPEN(0,f,e,p) -> {p} x = e; {q}` computes Q[e/x] with fol's judgements, all checked; program
variables must be parameters (`gcd.btp`: `rTm$A`, `rPar$A`, `PLT` chain after Z; tactics'
`add_program_vars`, `assign(x, e, q)`). `{q} x:=e {p}` is unsound (accepts any precondition).
Older style (`hoare.btp`, variables as constants): fix the assertion shape, one axiom per
program variable (side conditions unchecked), so Q[e/x] is just filling in `e`:
```
rAssignI : {EQ(a,DIV2(e))} $I = e; {EQ(a,DIV2($I))}   # a must not mention $I
rAssignS : {EQ(e,g)} $S = e; {EQ($S,g)}               # g must not mention $S
```
Keep assertions in shape by ordering: the increment comes *after* the `IF`, so stepping
back over `$I = S($I)` gives `EQ($S,DIV2(S($I)))`. Program text and conditions use library
notation (`EQ`, `¬`, `MOD2`), so `rIf`/`rWhile` put conditions into assertions as is, and
the verification conditions are library lemmas (`lib/parity.btp`), not axioms.
Extraction: a last block calls `lib/extract.py`'s `write_py(env, 'thProgram', fn, 'hoare.py', __file__)`,
which parses the *checked* triple from `env['theorems']` and writes Python (unassigned variables are
parameters, assigned ones in the postcondition the result, pre/post become `assert`s, or comments
when quantified). Trusted: its symbol table (MOD2 as `% 2`, MOD as `%`, `$` dropped, …; unknown
symbols are errors) and termination. `gcd.btp`: Euclid, invariant "same common divisors as
$X, $Y"; MOD by recursion (`rModWrap`/`rModNext`), `thModDiv`: a = b·q + MOD(a,b).
`bsearch.btp`: isqrt by binary search; tests need executable symbols, so it uses order's
predicate `LE` (extract reads it as `<=`); `thMidpoint`:
a+2 ≤ b ⇒ a < DIV2(a+b) < b (via parity's `thDiv2Add`, `thDiv2Le`).

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
`semiring.btp` (loads peano, nd; Python block): `thZeroAdd` … `thMulAssoc`, all closed ∀ sentences
(0+n = n, S(m)+n = S(m+n), + and · commutative and associative, distributivity, …).
`sum.btp` (loads peano): SUM(n) = 0+1+…+n by recursion; `gauss.btp` proves 2·SUM(n) = n·S(n).
`parity.btp` (loads semiring, nd; Python block): FLIP, MOD2, DIV2 by recursion; `thModDich`,
`thDiv2Odd`, `thDiv2Even`, `thDiv2SS`, `thDiv2Add` (DIV2(n+(m+m)) = DIV2(n)+m), `thDiv2Le`. `hoare.btp` (loads fol, strings): Hoare rules and program syntax.
`nd.btp` (loads logic; Python block): `thCurry`, `thC`, `thW`, `thCP2`, `thAbs`, `thLEM`, the
schemas natural deduction compiles to. `order.btp` (loads semiring, nd; Python block): ≤ is
∃k. b = a+k, < is S(a) ≤ b, as formulas; totality, cancellation, `thLeSuccNZ`, `thLeTwoNotOne`, …; `LE(a,b)`, ≤ as a
predicate for program tests (`rLeI`/`rLeE`, CT-guarded; tactics' `le_i`/`le_e` convert).
`divides.btp` (loads order): d|m is ∃c. m = d·c; `thDvdSucc`: p|a, p|S(a) ⇒ p = 1; `thDvdZero`,
`thDvdAdd`, `thDvdCancel` (d|a, d|a+b ⇒ d|b). `fact.btp` (loads divides): FACT, `thFactPos`,
`thDvdFact`; `primes.btp` proves Euclid's theorem on them.

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
parameter `w` (`PAR(w)`), others pass via `DIFF(w,o)`. In tactics, the step is
`root.close(c.discharge(...))` for `c = root.assume(instantiate(f, N_))`, the IH `c.hyp_()`
(semiring, gauss); no hand-rolled `thId`/`rK`/`thHS` plumbing, and none in assertion
VCs either (`hoare.btp`).

**Other inductive types** (`compiler.btp`). Structural induction like `rInd`, one parameter
per subterm (`rIndExp`: M, N, each with OPEN and ABS premises; IHs as curried premises
`⊢(h=>(g=>p))`). One sort, so it and `rInd` both say "every object is one of these"; consistent
because numbers can code the terms. Quantify the IH over everything that varies (`∀k∀s`), and
use continuations (`COMP(e,k)`) instead of appending lists. tactics' `induction_rule(rule, f,
side, premises)` builds the OPEN/ABS premises of any such rule (`induction`, `exp_induction`,
`no_regress` are calls to it). Constants register in `ATOM_RULES`,
`CT_ATOMS`, `OPEN_ATOMS`, `ABS_ATOMS`. Well-founded induction over a relation (`aquinas.btp`'s
`rNoRegress`): IH `ALL((MOVES(V(0),N)=>f))`, putting f as is under the new ∀ rebinds its V(0).

**Natural deduction in Python blocks** (`lib/tactics.py` `Ctx`, over `lib/nd.btp`). A proof
under hypotheses is a context formula G (⊤, then (G∧H) per assumption); a fact X there is
⊢(G=>X). `assume`, `hyp_`, `discharge` (thCurry), `mp`/`thru` (axiom S / HS), `and_i/l/r`,
`or_l/r`, `cases` (rOrE), `efq`, `absurd` (thAbs), `by_contra`, `lem`, `all_e`, `ex_i`, `all_i`
(rGen + `rAllImp`), `ex_e` (thC, rGen, `rExE`, thW), `nat_cases` (thZeroOrSucc, the S(p) case
unpacked), equations via `chain`/`trans`/`sym`; `subst(heq, h, path)` rewrites a = b inside any
formula built from EQ (∧ ∨ => ¬ ∀ ∃; ¬ and the left of => go back b to a). It re-derives per use, so
a lemma like `thDvdEq` checks shorter where one exists. Fresh
parameters come from K < M < … < Z; pass `reserved=` for the statement's own. Build formulas
with named parameters and `forall`/`exists`/`le`/`lt`/`dvd`/`prime`; `instantiate`/`abstract`
handle de Bruijn shifts (`parity.btp`: ∀n ∃k. n = k+k ∨ n = S(k+k)). Shared helpers (`snz`, `sinj`, `refl`,
`closed`, `gen_all`, `lemma`), library symbols (FLIP, MOD2, DIV2, FACT, SUM) and evaluation
(`add_eval`, `sum_eval`) live in tactics.py, not per block. Induction matrices may contain
quantifiers (`thPrimeFactor` is strong induction on a bound).

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
