//! Conversion to a Church-encoded `Term`

use term::Term;

/// Conversion to a Church-encoded lambda term
pub trait IntoChurch {
    /// Consume an object and return a Church-encoded `Term`
    fn into_church(self) -> Term;
}

/// This impl can optionally not be built using `default-features = false`.
#[cfg(feature = "church")]
impl<T> From<T> for Term where T:IntoChurch {
    fn from(t: T) -> Self {
        t.into_church()
    }
}
