# lambda_calculus

**lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

The data and operators follow the Church encoding. The terms are implemented using De Bruijn
indices, but can also be displayed using the classic lambda notation.

The library contains:

- Church numerals and arithmetic operations
- Church booleans
- Church pairs
- Church lists
- standard lambda terms and combinators
- a parser for lambda expressions with De Bruijn indices
- [7 β-reduction strategies](http://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf)
with optional display of reduction steps

The implementation tries to find a compromise between the spirit of the lambda calculus and Rust's
best practices; the lambda `Term`s implemented by the library are produced by functions (in order
to allow arbitrary application), but they are not `Copy`able and the methods they provide allow
memory-friendly disassembly and referencing their internals.

## [Documentation](https://docs.rs/lambda_calculus)

## Status

The library is already usable, but it is still a work in progress.

## TODO

- polish `CallByValue` and `HybridApplicative` orders (they have issues with the Z combinator)
- additional tests
- β-reduction parallelization (at least to some extent)?
- further optimizations
