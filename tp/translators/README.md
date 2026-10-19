# Translators

Programs that turn other formal systems into Budge-TP files, so `budge-tp.py` checks their proofs.
Both stream to standard output, so pipe them into the checker:

```
python3 translators/mm2btp.py translators/demo0.mm | python3 budge-tp.py
python3 translators/prolog2btp.py translators/zebra.pl | python3 budge-tp.py
```

Examples here:

| File | |
|---|---|
| `demo0.mm` | Metamath's introductory system: one theorem, `t = t` |
| `hol.mm` | Mario Carneiro's higher-order logic: 151 theorems, typed terms, λ, `$d` (0.3 s) |
| `zebra.pl` | Einstein's riddle: Prolog searches, Budge-TP checks the one derivation of the answer |
| `types.pl` | Simply typed λ-calculus: certifies `S : (α → β → γ) → (α → β) → α → γ`; `λx. x x` has no type (occurs check) |
| `miu.pl` | Hofstadter's MIU system, as in `examples/miu.btp`, with derivations bounded by a step count |

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
negation (`\+`), disjunction, if-then-else, arithmetic and other built-ins, assert/retract, `op/3`,
DCG rules. A query with no answer gives nothing to check.
