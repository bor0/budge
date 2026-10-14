# The Budge theorem prover

Budge-TP is a computer program that allows expressing formal systems and deriving theorems.

## Syntax

Every statement in a Budge-TP code is of the form:

```
r<name> : <expr> [-> <expr> -> ... -> <expr>]
t<name> : <ruleN> [x=X;y=Y;...] [arg1] [arg2] [...] [argn]
p<name> : <text>
<?py
<python code>
?>
<?py <python code> ?>
```

The syntax for `<name>` and `<expr>` is any string of characters except `':'` and `' '` (whitespace). Square brackets represent optional values.

Lowercase characters in a rule expression are considered a variable and will be used for substitution within the expressions.

Prose statements (`p<name>`) print their text prefixed with `-- `, interleaved with theorem results in source order. The prefix distinguishes prose from derived theorems (which always use `name : value` form) so prose cannot spoof a theorem result. Prose supports `!` suppression like theorems.

Python blocks are meta-programs: lines between `<?py` and `?>` (each on its own line), or the code in a one-line `<?py ... ?>`, are Python code, run with `__file__` (the Budge file), `env` (everything read and checked so far) and `load(path)` defined. Whatever the block prints is Budge code: it takes the block's place and is checked like any other code, so a wrong step is still rejected. `load` reads another Budge file, with the path relative to the current one: it is fully checked, its rules and theorems become available under the same names (a name clash is an error), it is loaded only once even if loaded several times, and its theorems and prose are not printed. Cycles are errors. This is how files use each other: `<?py load('lib/logic.btp') ?>`. Budge-TP itself provides nothing else; proof-building helpers are ordinary Python libraries. `--expand DIR` writes every loaded file with its blocks replaced by their output (keeping the `load` lines), so the proof can be checked without running any other Python.

```
python3 budge-tp.py proof.btp
python3 budge-tp.py --expand out proof.btp && python3 budge-tp.py out/proof.btp
```

## Semantics

The syntax `r<name>` specifies a rule, and `t<name>` specifies a theorem.

In a rule, all expressions but the last are considered the hypothesis (arguments to be passed when used in a theorem), and the last is the conclusion.

For theorems, the rule `<ruleN>` will be applied to the corresponding arguments. Substitution with theorems (`x` with theorem `X`; `y` with theorem `Y`...) will be performed in both the rule's hypotheses and the theorem's provided argument, and they will be matched/unified. If unification is successful, the final argument in the rule `argn` will be the result.

Budge-TP will print all derived theorems except those whose name ends in a `!`.

## Library

[`examples/lib`](./examples/lib) holds reusable theories:

- [logic.btp](./examples/lib/logic.btp) - Classical propositional logic in Hilbert's system (axioms K, S, contraposition, ∧, ∨, modus ponens), deriving identity, hypothetical syllogism, double negation elimination and introduction, contraposition, ex falso, disjunctive syllogism and commutativity of ∧ and ∨
- [fol.btp](./examples/lib/fol.btp) - First-order logic with equality: ∀ and ∃ with de Bruijn indices (capture-free instantiation, generalisation, ∃-elimination) and the equality axioms
- [peano.btp](./examples/lib/peano.btp) - The defining equations of + and ·, congruence, and induction
- [list.btp](./examples/lib/list.btp) - Lists of numbers, with list relations: append, car/cdr, membership, sum, max, substitution, reversal, sortedness

## Example

In the `examples` folder you can find the following proofs:

- [Gestalt](./examples/gestalt.btp) - Differentiation and contact in Gestalt therapy
- [God](./examples/God.btp) - Anselm's ontological argument as a contraposition, using the library
- [Automaton](./examples/automaton.btp) - A finite-state machine
- [Boolean](./examples/boolean.btp) - Boolean logic
- [Budge system (two-register)](./examples/budge-pl.btp) - Based on my [Budge programming language](https://github.com/bor0/budge/tree/main/pl)
- [CL](./examples/cl.btp) - Propositional logic with ∧ and ∨ by hand, using the library
- [Coordgame](./examples/coordgame.btp) - Game on coordinates implementation
- [DND](./examples/dnd.btp) - Prime numbers (divisibility)
- [Hanoi](./examples/hanoi.btp) - An implementation of the rules for Hanoi's tower
- [Hoare logic](./examples/hoare.btp) - Partial correctness proof of a tiny imperative program
- [List](./examples/list.btp) - List implementation and some example functions on them
- [LLM](./examples/llm.btp) - A toy bigram language model with greedy decoding
- [MU puzzle](./examples/miu.btp) - A simple usage of a small formal system
- [Peano's axioms](./examples/peano.btp) - A more detailed example on numbers
- [PQ](./examples/pq.btp) - Number addition
- [Run-Length Encoder decompressor](./examples/rle.btp) - Based on lists, an encoding/decoding algorithm
- [Quantifiers](./examples/quantifiers.btp) - First-order reasoning with ∀ and ∃ by hand, using the library
- [RSA](./examples/rsa.btp) - Toy RSA encryption and decryption using tally numbers
- [SKI calculus](./examples/ski.btp) - SKI calculus
- [TQ](./examples/tq.btp) - Number multiplication
- [Typed](./examples/typed.btp) - Shows the distinction between terms and theorems
- [Whirlpool](./examples/whirlpool.btp) - The self-referential trap of searching for escape, and cognitive defusion
- [Zero plus n](./examples/zero_plus_n_induction.btp) - Proof that 0 + n = n by induction
