# lambda_calculus
[![license](https://img.shields.io/badge/license-CC0-blue.svg)](https://creativecommons.org/publicdomain/zero/1.0/)
[![current version](https://img.shields.io/crates/v/lambda_calculus.svg)](https://crates.io/crates/lambda_calculus)
[![build status](https://api.travis-ci.org/ljedrz/lambda_calculus.svg?branch=master)](https://travis-ci.org/ljedrz/lambda_calculus)

**lambda_calculus** is a simple, zero-dependency implementation of pure lambda calculus in Safe Rust.

## [Documentation](https://docs.rs/lambda_calculus)

## Features

- a parser for lambda expressions, both in classic and De Bruijn index notation
- 7 β-reduction strategies
- a set of standard terms (combinators)
- lambda-encoded boolean, pair, tuple, option and result data types
- single-pair-encoded list
- Church-, Scott- and Parigot-encoded numerals and lists
- Stump-Fu (embedded iterators)- and binary-encoded numerals
- signed numbers

## Installation

Include the library by adding the following to your Cargo.toml:
```
[dependencies]
lambda_calculus = "^3.0"
```

And the following to your code:
```
#[macro_use]
extern crate lambda_calculus;
```

Compilation features:
- `backslash_lambda`: changes the display of lambdas from `λ` to `\`
- `encoding`: builds the data encoding modules; default feature

Example feature setup in Cargo.toml:
```
[dependencies.lambda_calculus]
version = "^3.0"
default-features = false # do not build the data encoding modules
features = ["backslash_lambda"] # use a backslash lambda
```

## Examples

### Comparing classic and De Bruijn index notation

code:
```
use lambda_calculus::data::num::church::{succ, pred};

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
use lambda_calculus::*;

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
use lambda_calculus::data::num::church::pred;

fn main() {
    let mut expr = app!(pred(), 1.into_church());

    println!("{} order β-reduction steps for PRED 1 are:", NOR);

    println!("{}", expr);
    while expr.reduce(NOR, 1) != 0 {
        println!("{}", expr);
    }
}
```
stdout:
```
normal order β-reduction steps for PRED 1 are:
(λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b)
λa.λb.(λc.λd.c d) (λc.λd.d (c a)) (λc.b) (λc.c)
λa.λb.(λc.(λd.λe.e (d a)) c) (λc.b) (λc.c)
λa.λb.(λc.λd.d (c a)) (λc.b) (λc.c)
λa.λb.(λc.c ((λd.b) a)) (λc.c)
λa.λb.(λc.c) ((λc.b) a)
λa.λb.(λc.b) a
λa.λb.b
```

### Comparing the number of steps for different reduction strategies

code:
```
use lambda_calculus::*;
use lambda_calculus::data::num::church::fac;

fn main() {
    let expr = app(fac(), 3.into_church());

    println!("comparing normalizing orders' reduction step count for FAC 3:");
    for &order in [NOR, APP, HNO, HAP].iter() {
        println!("{}: {}", order, expr.clone().reduce(order, 0));
    }
}
```
stdout:
```
comparing normalizing orders' reduction step count for FAC 3:
normal: 46
applicative: 39
hybrid normal: 46
hybrid applicative: 39
```

### Comparing different numeral encodings

code:
```
use lambda_calculus::*;

fn main() {
    println!("comparing different encodings of number 3 (De Bruijn indices):");
    println!("  Church encoding: {:?}", 3.into_church());
    println!("   Scott encoding: {:?}", 3.into_scott());
    println!(" Parigot encoding: {:?}", 3.into_parigot());
    println!("Stump-Fu encoding: {:?}", 3.into_stumpfu());
    println!("  binary encoding: {:?}", 3.into_binary());
}
```
stdout:
```
comparing different encodings of number 3 (De Bruijn indices):
  Church encoding: λλ2(2(21))
   Scott encoding: λλ1(λλ1(λλ1(λλ2)))
 Parigot encoding: λλ2(λλ2(λλ2(λλ1)1)(2(λλ1)1))(2(λλ2(λλ1)1)(2(λλ1)1))
Stump-Fu encoding: λλ2(λλ2(2(21)))(λλ2(λλ2(21))(λλ2(λλ21)(λλ1)))
  binary encoding: λλλ1(13)
```
