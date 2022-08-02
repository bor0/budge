# The Arrew theorem prover

Arrew (ARrow REWriter) is a computer program that allows expressing formal systems and deriving theorems.

## Syntax

Every statement in an Arrew code is of the form:

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

Arrew will print all derived theorems except those whose name ends in a `!`.

## Example

In the [MU puzzle](./examples/miu.arw) example we provide a simple usage of a small formal system.

We implement number addition and multiplication with the [PQ](./examples/pq.arw) and [TQ](examples/tq.arw) system respectively. Prime numbers with the [DND](examples/dnd.arw) system. See [Peano's axioms](./examples/peano.arw) for a more detailed example on numbers.

See [Gentzen](./examples/gentzen.arw) and [SKI calculus](./examples/ski.arw) for logical systems.

There is an implementation of [lists](examples/list.arw), as well as a system for [coordinates](./examples/coord.arw) and a small [game](./examples/coordgame.arw).

There's also an implementation of a [two-register Budge system](./examples/budge.arw), based on my [Budge programming language](https://github.com/bor0/budge).

## Development

Install `pre-commit` and configure it once you clone this repo:

```
$ pip3 install pre-commit
$ pre-commit install
```
