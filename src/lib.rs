//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

#![deny(missing_docs)]

#[macro_use]

pub mod term;
pub mod reduction;
pub mod arithmetic;
pub mod booleans;
pub mod pair;
pub mod list;
pub mod combinators;
pub mod parser;
