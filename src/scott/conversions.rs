//! Conversion to a Scott-encoded `Term`

use term::Term;

/// Conversion to a Scott-encoded lambda term
pub trait IntoScott {
    /// Consume an object and return a Scott-encoded `Term`
    fn into_scott(self) -> Term;
}

/// This impl can optionally be built using `features = scott`.
#[cfg(feature = "scott")]
impl<T> From<T> for Term where T:IntoScott {
    fn from(t: T) -> Self {
        t.into_scott()
    }
}
