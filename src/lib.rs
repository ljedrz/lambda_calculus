//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

#![deny(missing_docs)]

#[macro_use]

pub mod term;
pub mod parser;
pub mod reduction;
pub mod combinators;
pub mod church;
