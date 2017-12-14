//! Conversion to Church-encoded `Term`s

use term::Term;

/// Conversion to Church encoding
pub trait IntoChurch {
    /// Convert an object into a Church-encoded `Term`
    fn into_church(self) -> Term;
}
