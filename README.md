# lambda_calculus
[![license](https://img.shields.io/badge/license-CC0-blue.svg)](https://creativecommons.org/publicdomain/zero/1.0/)
[![current version](https://img.shields.io/crates/v/lambda_calculus.svg)](https://crates.io/crates/lambda_calculus)
[![build status](https://api.travis-ci.org/ljedrz/lambda_calculus.svg?branch=master)](https://travis-ci.org/ljedrz/lambda_calculus)

**lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

## [Documentation](https://docs.rs/lambda_calculus)

## Features

- a parser for lambda expressions, both in classic and De Bruijn index notation
- 7 β-reduction strategies with optional display of reduction steps
- a set of standard terms (combinators)
- Church-encoded numerals, booleans, pair, list and option
- Scott-encoded numerals
- Parigot-encoded numerals

## Installation

Include the library by adding the following to your Cargo.toml:
```
[dependencies]
lambda_calculus = "^2.0"
```

And the following to your code:
```
#[macro_use]
extern crate lambda_calculus;
```

Compilation features:
- `backslash_lambda`: changes the display of lambdas from `λ` to `\`
- `church`: builds the `church` module; default feature
- `scott`: builds the `scott` module
- `parigot`: builds the `parigot` module

note: only one encoding module can be used at a time

To apply a feature setup the dependency in your Cargo.toml like this:
```
[dependencies.lambda_calculus]
version = "^2.0"
default-features = false # do not build the church module
features = ["backslash_lambda", "parigot"] # use a backslash lambda and the Parigot encoding
```

## Usage

### Comparing classic and De Bruijn index notation

code:
```
use lambda_calculus::church::numerals::{succ, pred};

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
use lambda_calculus::church::numerals::pred;

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
use lambda_calculus::church::numerals::fac;

fn main() {
    let expr = app!(fac(), 4.into());

    compare(&expr, &[NOR, APP, HNO, HAP], false); // compare normalizing strategies
}
```
stdout:
```
comparing β-reduction strategies for (λa.a (λb.λc.λd.b (λe.c (d e)) (λe.λf.e (d e f))) (λb.λc.b) (λb.λc.b c) (λb.λc.b c)) (λa.λb.a (a (a (a b)))):

normal:             87
applicative:        65
hybrid normal:      87
hybrid applicative: 40
```
