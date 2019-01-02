//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

#![deny(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
pub mod term;
pub mod parser;
pub mod reduction;
pub mod combinators;

pub use self::term::{Term, abs, app, UD};
pub use self::term::Term::*;
pub use self::term::Notation::*;
pub use self::reduction::beta;
pub use self::reduction::Order::*;
pub use self::parser::parse;

#[cfg(feature = "encoding")]
pub mod data;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::*;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::Encoding::*;
#[cfg(feature = "encoding")]
pub use crate::data::list::convert::*;
