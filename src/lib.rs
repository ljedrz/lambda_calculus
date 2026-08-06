//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.
//!
//! # Stack depth
//!
//! Reduction, and every other operation on a [`Term`], walks a tree of boxes
//! recursively, so stack use scales with how deeply nested the term is. Deep enough and
//! the process dies on a guard page — a `SIGSEGV` with no unwinding, no panic message
//! and no failing assertion.
//!
//! Two unrelated things cause that, and only one of them is cured by a bigger stack.
//!
//! An **unbounded reduction** is not: an applicative-family order ([`APP`], [`HAP`])
//! applied to a term built on a recursion combinator never converges, so it exhausts
//! whatever stack it is given. The functions this affects say so under `# Errors`; the
//! answer is a normal-order strategy, not a larger `stack_size`.
//!
//! A **genuinely deep term** is, because its depth is bounded by the input. That is
//! worth measuring rather than guessing, and it can be measured without instrumenting
//! anything — see the `Stack depth` section of the README for how, and for the figures
//! this crate's own `tests/stack_depth.rs` pins down. The short version: nesting costs
//! roughly 0.5 KiB per level unoptimized for [`beta`] and [`Term::clone`], and about
//! four times that for [`Debug`](std::fmt::Debug) — which is the path `assert_eq!`
//! takes when it fails, so comparing terms more than ~1000 levels deep aborts while
//! rendering the mismatch instead of reporting it.
//!
//! [`APP`]: crate::reduction::Order::APP
//! [`HAP`]: crate::reduction::Order::HAP

#![deny(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
pub mod term;
pub mod combinators;
pub mod parser;
pub mod reduction;

pub use self::parser::{parse, parse_with_context};
pub use self::reduction::Order::*;
pub use self::reduction::beta;
pub use self::reduction::eta;
pub use self::term::Notation::*;
pub use self::term::Term::*;
pub use self::term::{Term, UD, abs, app};

#[cfg(feature = "encoding")]
pub mod data;
#[cfg(feature = "encoding")]
pub use crate::data::list::convert::*;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::Encoding::*;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::*;
