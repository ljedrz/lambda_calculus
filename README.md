# lambda_calculus
[![license](https://img.shields.io/badge/license-CC0-blue.svg)](LICENSE)
[![current version](https://img.shields.io/crates/v/lambda_calculus.svg)](https://crates.io/crates/lambda_calculus)

**lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

The data and operators follow the Church encoding. The terms are implemented using De Bruijn
indices, but are displayed using the classic lambda notation and can be parsed both ways. Library
functions utilizing the fixed-point combinator use its call-by-value variant and are built for
compatibility with as many β-reduction strategies as possible.

The library contains:

- Church numerals and arithmetic operations
- Church booleans
- Church pairs
- Church lists
- standard terms (combinators)
- a parser for lambda expressions
- 7 β-reduction strategies with optional display of reduction steps

The implementation tries to find a compromise between the spirit of the lambda calculus and Rust's
best practices; the lambda `Term`s implemented by the library are produced by functions (in order
to allow arbitrary application), but they are not `Copy`able and the methods they provide allow
memory-friendly disassembly and referencing their internals.

## [Documentation](https://docs.rs/lambda_calculus)

## Example usage

code:
```
// SHOW_REDUCTIONS [@reduction.rs] = true;

#[macro_use]
extern crate lambda_calculus;

use lambda_calculus::reduction::Order::*;
use lambda_calculus::arithmetic::pred;

fn main() {
    let mut expr = app!(pred(), 1.into());

    expr.beta(NOR, 0);
}
```
stdout:
```
β-reducing (λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b) [normal order]:

1. (λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b)
=>     λa.λb.(λc.λd.c d) (λc.λd.d (c a)) (λc.b) (λc.c)

2. (λc.λd.c d) (λc.λd.d (c a))
=>     λc.(λd.λe.e (d a)) c

3. (λc.(λd.λe.e (d a)) c) (λc.b)
=>     (λc.λd.d (c a)) (λc.b)

4. (λc.λd.d (c a)) (λc.b)
=>     λc.c ((λd.b) a)

5. (λc.c ((λd.b) a)) (λc.c)
=>     (λc.c) ((λc.b) a)

6. (λc.c) ((λc.b) a)
=>     (λc.b) a

7. (λc.b) a
=>     b

result after 7 reductions: λa.λb.b
```

## Status

The library is in a good shape and should soon begin to stabilize.

## TODO

- shortened display mode/function (λa.λb.λc. => λabc.)
- additional tests
- further optimizations; β-reduction parallelization (at least to some extent)?
