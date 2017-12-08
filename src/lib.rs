//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

#![deny(missing_docs)]

#[macro_use]

pub mod term;
pub mod parser;
pub mod reduction;
pub mod combinators;
#[cfg(not(feature = "no_church"))]
pub mod church;

pub use self::term::{Term, abs, app};
pub use self::term::Term::*;
pub use self::term::Notation::*;
pub use self::reduction::beta;
pub use self::reduction::Order::*;
pub use self::parser::parse;
