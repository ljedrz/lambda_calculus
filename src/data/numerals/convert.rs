//! Conversions to different `Term` encodings

use term::Term;

/// Conversion to Church encoding
pub trait IntoChurch {
    /// Convert an object into a Church-encoded `Term`
    fn into_church(self) -> Term;
}

/// Conversion to Scott encoding
pub trait IntoScott {
    /// Convert an object into a Scott-encoded `Term`
    fn into_scott(self) -> Term;
}

/// Conversion to Parigot encoding
pub trait IntoParigot {
    /// Convert an object into a Parigot-encoded `Term`
    fn into_parigot(self) -> Term;
}

/// Conversion to Stump-Fu encoding
pub trait IntoStumpFu {
    /// Convert an object into a Stump-Fu-encoded `Term`
    fn into_stumpfu(self) -> Term;
}
