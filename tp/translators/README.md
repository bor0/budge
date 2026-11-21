# Translators

Programs that turn other formal systems into Budge-TP files, so `budge-tp.py` checks their proofs.
Both stream to standard output, so pipe them into the checker (`--pure`: it runs no Python, so
nothing a translator writes can be more than rules and theorems to check):

```
python3 translators/mm2btp.py translators/demo0.mm | python3 budge-tp.py --pure
python3 translators/prolog2btp.py translators/zebra.pl | python3 budge-tp.py --pure
```

Examples here:

| File | |
|---|---|
| `demo0.mm` | Metamath's introductory system: one theorem, `t = t` |
| `hol.mm` | Mario Carneiro's higher-order logic: 151 theorems, typed terms, λ, `$d` (0.3 s) |
| `zebra.pl` | Einstein's riddle: Prolog searches, Budge-TP checks the one derivation of the answer |
| `types.pl` | Simply typed λ-calculus: certifies `S : (α → β → γ) → (α → β) → α → γ`; `λx. x x` has no type (occurs check) |
| `miu.pl` | Hofstadter's MIU system, as in `examples/miu.btp`, with derivations bounded by a step count |
| `neural.pl` | A neural network learns XOR by backpropagation: one epoch of training, and the trained weights compute XOR (13,773 steps, most of them arithmetic) |

## mm2btp.py: Metamath

```
python3 translators/mm2btp.py <db.mm> [--stop LABEL]
```

Each assertion becomes a sequent `⟦ H1 ⨾ … ⨾ Hn ⟧ ⟹ C`: its `$f` and `$e` hypotheses, then the floats
of dummy variables and the `$d` pairs as `DISJ ⟨ x ⟩ ⟨ y ⟩`. `$a` statements are rules; a `$p`
proof is replayed into Budge-TP steps under the theorem's own hypotheses, and a proved sequent is
used as a rule by later proofs. Budge-TP checks every step; trusted are the translated `$a` rules
and a few structural rules (`rApplyN`, `rLeaf`, `rInL`/`rInR`, `rNode`, `rFlatN`, `rWeaken`,
`rDisj…`). Variables become Unicode lowercase letters (`ph` → `φ`), constants tokens without
lowercase letters (`wff` → `WFF`, `|-` → `⊢`).

Dummy variables can't be discharged in Budge-TP (that needs "d does not occur in Γ"), so they stay
as premises: Specker's `nchoice` in nf.mm checks as "given 22 suitably distinct fresh variables,
⊢ ¬ <_C WE NC".

Checked: `demo0.mm`, `hol.mm` (151 theorems), `big-unifier.mm`, `ql.mm` (1140), `nf.mm` (5976;
57 s, 12 GB), `set.mm` up to `ax-pow` (5190). Not supported: substituting the empty expression
(`miu.mm`), `$[` includes. Full `set.mm` runs out of memory. Databases:
<https://github.com/metamath/set.mm>.

## prolog2btp.py: Prolog

```
python3 translators/prolog2btp.py <program.pl> [--query GOAL]... [--all] [--max-steps N]
```

Each clause `H :- B1, …, Bn.` becomes a rule `B1 -> … -> Bn -> H`, terms written in full
(`f(a, [X|T])` as `F(A,[x|t])`, atoms uppercase, clause variables lowercase), so substituting text is
substituting terms. Budge-TP has no search or unification, so a small SLD engine (depth first, with
the occurs check and cut) runs the queries (`?- G.` in the file, or `--query`) and writes each
answer's proof tree as theorems: one per resolution step, naming the clause and the value of each of
its variables. The engine is not trusted; Budge-TP checks every step. Unbound variables left in an
answer become Greek letters: the theorem holds for every value of them.

`!` and `true` have no logical content and are dropped from the rules, so a proof is a proof from
the clauses read as implications; `X = Y` is proved by `rEq : =(x,x)`. Not supported (an error):
negation (`\+`), disjunction, if-then-else, other built-ins, assert/retract, `op/3`, DCG rules. A
query with no answer gives nothing to check.

Arithmetic: `is/2` and `<`, `>`, `=<`, `>=`, `=:=`, `=\=` over `+ - * / // mod` and `exp`. Numbers
are numerals with at most four decimals (`0.5`, `-12`, `2.71828` reads as `2.7182`), one type:
sums are exact, `*`, `/` and `exp` cut their results to four decimals, `//` rounds toward zero,
`mod` takes the sign of the divisor, `exp(x)` needs `|x| < 100`. A program that uses them gets
built-in rules (named `$…`) that the checker uses like any other:

- digit tables `$SUM` (a + b + carry) and `$PROD`, then `+`, `×` and `<` on digit strings column by
  column, the carries coming back up the string (`rAddcS : $SUM(a,b,k,c,i) -> $ADDC(x,y,i,z,j) ->
  $ADDC(xa,yb,k,zc,j)`);
- a numeral is its digits times 10⁴ (`$SC(0.5,05000)`), so a sum of numerals is a sum of integers,
  and a product drops the last four digits of the integer product;
- a quotient is checked rather than computed: `q = x / y` because `q·y + r = x` and `r < y`;
- `exp(x)` multiplies one table entry `e^(d·10^j)` per digit `d` of `x`, and `e^-x = 1 / e^x`;
- `$EVAL(e,v)` follows the expression, and `rIs : $EVAL(e,x) -> IS(x,e)` closes `X is E`.

The trusted part is the 310 digit facts and the 60 values of `e^(d·10^j)`, rounded to four decimals.
prolog2btp.py computes each result in Python and writes its proof directly (no search).
