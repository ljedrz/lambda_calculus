# lambda_calculus
[![CI](https://github.com/ljedrz/lambda_calculus/actions/workflows/ci.yml/badge.svg)](https://github.com/ljedrz/lambda_calculus/actions/workflows/ci.yml)
[![license](https://img.shields.io/badge/license-CC0-blue.svg)](https://creativecommons.org/publicdomain/zero/1.0/)
[![current version](https://img.shields.io/crates/v/lambda_calculus.svg)](https://crates.io/crates/lambda_calculus)
[![docs.rs](https://docs.rs/lambda_calculus/badge.svg)](https://docs.rs/lambda_calculus)

**lambda_calculus** is a simple, zero-dependency implementation of pure lambda calculus in Safe Rust.

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
```toml
[dependencies]
lambda_calculus = "3"
```

Compilation features:
- `backslash_lambda`: changes the display of lambdas from `λ` to `\`
- `encoding`: builds the data encoding modules; default feature

Example feature setup in Cargo.toml:
```toml
[dependencies.lambda_calculus]
version = "3"
default-features = false # do not build the data encoding modules
features = ["backslash_lambda"] # use a backslash lambda
```

## Examples

### Comparing classic and De Bruijn index notation

code:
```rust
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
```rust
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
```rust
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
```rust
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
```rust
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

## Stack depth

Reduction, and every other operation on a `Term`, walks a tree of boxes recursively, so
stack use scales with how deeply nested the term is. Deep enough and the process dies on
a guard page: a `SIGSEGV` with no unwinding, no panic message and no failing assertion.

Two unrelated things cause that, and only one of them is cured by a bigger stack.

**An unbounded reduction.** An applicative-family order (`APP`, `HAP`) applied to a term
built on a recursion combinator never converges — it exhausts whatever stack it is given.
Reducing `scott::add 1 2` under `HAP` costs ~192 bytes per step and never finishes; under
`NOR` it finishes in 16 steps and 9 KiB. The remedy is the strategy, not `stack_size`.

**A genuinely deep term.** Here the depth is bounded by the input, so a larger stack is
the right answer — and worth measuring rather than guessing. [`stackler`] reports what a
reduction actually touched, without instrumenting the code under measurement:

```rust
let (result, peak) = stackler::measure_peak(|| beta(expr, HAP, 0));
println!("peak stack use: {} bytes", peak.unwrap().bytes());
```

Its default paint depth is 256 KiB, which is far short of a large reduction; raise
`Stackler::paint_depth` past the expected peak or the reading comes back as
`Peak::AtLeast`, a lower bound rather than a measurement. Measured on the `reduction_huge`
test, which reduces a Church-encoded factorial of 10 under `HAP`:

| profile | peak stack |
| :--- | ---: |
| `--release` | 221 MiB |
| debug | 1.08 GiB |

Note the 5x between profiles: a `stack_size` tuned against a release build will not
survive `cargo test`. Per nesting level, for the individual operations:

| operation | debug | release | max depth on 2 MiB (debug) |
| :--- | ---: | ---: | ---: |
| `drop` | 208 B | 64 B | ~10000 |
| `Debug` | 513 B | 129 B | ~4000 |
| `clone`, `PartialEq`, `beta`, `eta` | 545 B | 128 B | ~3800 |
| `Display` | 802 B | 192 B | ~2600 |

Note that `libtest` gives each test a 2 MiB stack, not the 8 MiB of a main thread, so the
last column is the budget the test suite actually works against. `Display` is currently
the deepest path, and `Debug` matters out of proportion to its cost because it is what
`assert_eq!` invokes when it fails: past that depth a mismatch aborts while being rendered
instead of being reported. `tests/stack_depth.rs` keeps all of these figures honest.

Both formatting impls write directly into the `Formatter` rather than building a `String`
per subterm. That is what keeps their frames small, and it also makes them linear: the
older String-returning version copied each subtree's rendering into a fresh allocation at
every level, which is quadratic for a linear chain — the shape a Church numeral has.
Rendering a 32000-level chain went from 409 ms to 2.9 ms for `Display` and 107 ms to
1.1 ms for `Debug`. The trade is that neither impl honours width or precision specifiers
(`{:>20?}` no longer pads), which is the usual cost of streaming a recursive structure.

[`stackler`]: https://crates.io/crates/stackler
