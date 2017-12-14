//! Conversion to Scott-encoded `Term`s

use term::Term;

/// Conversion to Scott encoding
pub trait IntoScott {
    /// Convert an object into a Church-encoded `Term`
    fn into_scott(self) -> Term;
}
