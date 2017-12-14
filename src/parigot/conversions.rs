//! Conversion to a Parigot-encoded `Term`

use term::Term;

/// Conversion to a Parigot-encoded lambda term
pub trait IntoParigot {
    /// Consume an object and return a Parigot-encoded `Term`
    fn into_parigot(self) -> Term;
}


/// This impl can optionally be built using `features = parigot`.
#[cfg(feature = "parigot")]
impl<T> From<T> for Term where T:IntoParigot {
    fn from(t: T) -> Self {
        t.into_parigot()
    }
}
