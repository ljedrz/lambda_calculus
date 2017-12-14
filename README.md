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
- `encoding`: builds the encoding modules; default feature

Example feature setup in Cargo.toml:
```
[dependencies.lambda_calculus]
version = "^2.0"
default-features = false # do not build the encoding modules
features = ["backslash_lambda"] # use a backslash lambda
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
    assert_eq!(
        parse(&"λa.λb.λc.b (a b c)", Classic),
        parse(&"λλλ2(321)", DeBruijn)
    );
}
```

### Showing β-reduction steps

code:
```
use lambda_calculus::*;
use lambda_calculus::church::numerals::pred;

fn main() {
    let expr = app!(pred(), 1.into_church());
    let steps = beta_verbose(expr, NOR, 0);

    println!("the {} β-reduction steps for PRED 1 are:", NOR);

    for (step, ref term) in steps.iter().enumerate() {
        println!("{}: {}", step, term);
    }
}
```
stdout:
```
the normal β-reduction steps for PRED 1 are:
0: (λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b)
1: λa.λb.(λc.λd.c d) (λc.λd.d (c a)) (λc.b) (λc.c)
2: λa.λb.(λc.(λd.λe.e (d a)) c) (λc.b) (λc.c)
3: λa.λb.(λc.λd.d (c a)) (λc.b) (λc.c)
4: λa.λb.(λc.c ((λd.b) a)) (λc.c)
5: λa.λb.(λc.c) ((λc.b) a)
6: λa.λb.(λc.b) a
7: λa.λb.b
```

### Comparing the number of steps for different reduction strategies

code:
```
use lambda_calculus::*;
use lambda_calculus::reduction::compare;
use lambda_calculus::church::numerals::fac;

fn main() {
    let expr = app!(fac(), 4.into_church());
    let mut comparison = compare(&expr, &[NOR, APP, HNO, HAP]); // these are normalizing strategies
    comparison.sort_by_key(|p| p.1); // sort by the reduction count

    println!("comparing normalizing reduction step count for FAC 4:");

    for (order, count) in comparison {
        println!("{}: {}", order, count);
    }
}
```
stdout:
```
comparing normalizing reduction step count for FAC 4:
hybrid applicative: 40
applicative: 65
normal: 87
hybrid normal: 87
```
