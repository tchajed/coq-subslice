# subslice

[![CI](https://github.com/tchajed/coq-subslice/actions/workflows/coq-action.yml/badge.svg)](https://github.com/tchajed/coq-subslice/actions/workflows/coq-action.yml)

A Coq implementation of subslicing of lists. We implement a function `subslice` with the behavior of array indexing in both Python and Go, for example (with syntax `a[n:m]` in those languages). Subslicing is a generalization of the standard library `firstn` and `skipn` list operations, and is internally implemented with these functions.

Many theorems are proven showing simplifications of combinations of subslice, firstn and skipn, including lengths of the built lists. These operations accept nats as inputs and have well-defined behavior for out-of-bounds inputs (as opposed to accepting Fin.t arguments); as much as possible, theorems have minimal premises and apply even for out-of-bound arguments.
