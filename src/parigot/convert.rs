//! Conversion to Parigot-encoded `Term`s

use term::Term;

/// Conversion to Parigot encoding
pub trait IntoParigot {
    /// Convert an object into a Church-encoded `Term`
    fn into_parigot(self) -> Term;
}