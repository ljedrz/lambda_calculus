# lambda_calculus
[![license](https://img.shields.io/badge/license-CC0-blue.svg)](https://creativecommons.org/publicdomain/zero/1.0/)
[![current version](https://img.shields.io/crates/v/lambda_calculus.svg)](https://crates.io/crates/lambda_calculus)
[![build status](https://api.travis-ci.org/ljedrz/lambda_calculus.svg?branch=master)](https://travis-ci.org/ljedrz/lambda_calculus)

**lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

The library tries to find a compromise between the spirit of the lambda calculus and Rust's
best practices; the lambda `Term`s implemented by the library are produced by functions (in order
to allow arbitrary application), but they are not `Copy`able and the methods they provide allow
memory-friendly disassembly and referencing their internals.

## [Documentation](https://docs.rs/lambda_calculus)

## Features

- Church numerals and arithmetic operations
- Church booleans
- Church pairs
- Church lists
- standard terms (combinators)
- a parser for lambda expressions
- 7 β-reduction strategies with optional display of reduction steps

The data and operators follow the Church encoding. The terms are implemented using De Bruijn
indices, but are displayed using the classic lambda notation and can be parsed both ways. Library
functions utilizing the fixed-point combinator use its call-by-value variant and are built for
compatibility with as many β-reduction strategies as possible.

## Installation

Include the library by adding the following to your Cargo.toml:
```
[dependencies]
lambda_calculus = "0.12.0"
```

And the following to your code:
```
#[macro_use]
extern crate lambda_calculus;
```

## Usage

### Comparing classic and De Bruijn index notation

code:
```
use lambda_calculus::arithmetic::{succ, pred};

fn main() {
    println!("SUCC := {0} = {0:?}", succ());
    println!("PRED := {0} = {0:?}", pred());
}
```
stdout:
```
SUCC := λa.λb.λc.b (a b c) = λλλ2(321)
PRED := λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d) = λλλ3(λλ1(24))(λ2)(λ1)
```

### Parsing lambda expressions

code:
```
use lambda_calculus::parser::*;

fn main() {
    assert_eq!(parse(&"λa.λb.λc.b (a b c)", Classic), parse(&"λλλ2(321)", DeBruijn));
}
```

### Showing β-reduction steps

code:
```
use lambda_calculus::reduction::*;
use lambda_calculus::arithmetic::pred;

fn main() {
    let mut expr = app!(pred(), 1.into());

    expr.beta(NOR, 0, true);
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

### Comparing the number of steps of different reduction strategies

code:
```
use lambda_calculus::reduction::*;
use lambda_calculus::arithmetic::fac;

fn main() {
    let expr = app!(fac(), 4.into());

    compare(&expr, &[NOR, APP, HNO, HAP], false);
}
```
stdout:
```
comparing β-reduction strategies for (λa.a (λb.λc.λd.b ((λe.λf.λg.e (f g)) c d) ((λe.λf.λg.f (e f g)) d)) (λb.λc.b) (λb.λc.b c) (λb.λc.b c)) (λa.λb.a (a (a (a b)))):

normal:             118
applicative:        68
hybrid normal:      118
hybrid applicative: 52
```

## Status

The library is in a good shape and should soon begin to stabilize.

## TODO

- normalize `Term`-producing functions
- further optimizations
- additional tests
- β-reduction parallelization (at least to some extent)?
- shortened display mode/function (λa.λb.λc. => λabc.)?
