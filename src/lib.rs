//! **lambda_calculus** is a simple implementation of the untyped lambda calculus in Rust.

#![deny(missing_docs)]
#![deny(unsafe_code)]

#[macro_use]
pub mod term;
pub mod combinators;
pub mod parser;
pub mod reduction;

pub use self::parser::parse;
pub use self::reduction::beta;
pub use self::reduction::Order::*;
pub use self::term::Notation::*;
pub use self::term::Term::*;
pub use self::term::{abs, app, Term, UD};

#[cfg(feature = "encoding")]
pub mod data;
#[cfg(feature = "encoding")]
pub use crate::data::list::convert::*;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::Encoding::*;
#[cfg(feature = "encoding")]
pub use crate::data::num::convert::*;
