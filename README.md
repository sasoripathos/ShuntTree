# ShuntTree
Shunt Tree is a balanced tree structure aiming to support parallel programming in pure functional programming. The idea was proposed by [Morihata and Matsuzaki (2011)](https://dl.acm.org/doi/10.1145/2034773.2034791).

This project provides an implementation in Scala 3 and formally verify the correctness via the [Stainless verification framework](https://gitlab.epfl.ch/lara/stainless)

# How to run

## Requirement
Java Development Kit 17, Stainless, Scala (coursier is recommended).

## Execute the code

```
# Remember to add --solvers=smt-z3 if on MacOS
> stainless src/*.scala --functions=<name of the functions you are working on>
# E.g.
> stainless src/*.scala --functions=negationNormalForm,skolemizationNegation

```