//! Conversion to Stump-Fu-encoded `Term`s

use term::Term;

/// Conversion to Stump-Fu encoding
pub trait IntoStumpFu {
    /// Convert an object into a Stump-Fu-encoded `Term`
    fn into_stumpfu(self) -> Term;
}
