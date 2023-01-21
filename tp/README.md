# The Budge theorem prover

Budge-TP is a computer program that allows expressing formal systems and deriving theorems.

## Syntax

Every statement in a Budge-TP code is of the form:

```
r<name> : <expr> [-> <expr> -> ... -> <expr>]
t<name> : <ruleN> [x=X;y=Y;...] [arg1] [arg2] [...] [argn]
```

The syntax for `<name>` and `<expr>` is any string of characters except `':'` and `' '` (whitespace). Square brackets represent optional values.

Lowercase characters in a rule expression are considered a variable and will be used for substitution within the expressions.

## Semantics

The syntax `r<name>` specifies a rule, and `t<name>` specifies a theorem.

In a rule, all expressions but the last are considered the hypothesis (arguments to be passed when used in a theorem), and the last is the conclusion.

For theorems, the rule `<ruleN>` will be applied to the corresponding arguments. Substitution with theorems (`x` with theorem `X`; `y` with theorem `Y`...) will be performed in both the rule's hypotheses and the theorem's provided argument, and they will be matched/unified. If unification is successful, the final argument in the rule `argn` will be the result.

Budge-TP will print all derived theorems except those whose name ends in a `!`.

## Example

In the `examples` folder you can find the following proofs:

- [God](./examples/God.btp) - Simpler variant of Anselm's argument
- [Automaton](./examples/automaton.btp) - A finite-state machine
- [Boolean](./examples/boolean.btp) - Boolean logic
- [Budge system (two-register)](./examples/budge-pl.btp) - Based on my [Budge programming language](https://github.com/bor0/budge/tree/main/pl)
- [CL](./examples/cl.btp) - Combinatory logic
- [Coord](./examples/coord.btp) - Coordinates implementation
- [Coordgame](./examples/coordgame.btp) - Game on coordinates implementation
- [DND](./examples/dnd.btp) - Prime numbers (divisibility)
- [Gentzen](./examples/gentzen.btp) - Gentzen system
- [Hanoi](./examples/hanoi.btp) - An implementation of the rules for Hanoi's tower
- [Hilbert's system](./examples/hilbert.btp) - Hilbert's logical system
- [List](examples/list.btp) - List implementation and some example functions on them
- [MU puzzle](./examples/miu.btp) - A simple usage of a small formal system
- [Peano's axioms](./examples/peano.btp) - A more detailed example on numbers
- [PQ](./examples/pq.btp) - Number addition
- [Run-Length Encoder decompressor](./examples/rle.btp) - Based on lists, an encoding/decoding algorithm
- [SKI calculus](./examples/ski.btp) - SKI calculus
- [TQ](./examples/tq.btp) - Number multiplication
