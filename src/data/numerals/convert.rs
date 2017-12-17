//! Conversions to different `Term` encodings

#![allow(missing_docs)]

use term::{Term, abs, app};
use term::Term::*;

/// The encoding type applicable to numerals.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Encoding {
    /// Church encoding
    Church,
    /// Scott encoding
    Scott,
    /// Parigot encoding
    Parigot,
    /// Stump-Fu (embedded iterators) encoding
    StumpFu
}

macro_rules! make_trait {
    ($trait_name:ident, $function_name:ident) => (
        pub trait $trait_name {
            #[doc="Performs the conversion."]
            fn $function_name(self) -> Term;
        }
    );
}

make_trait!(IntoChurch, into_church);
make_trait!(IntoScott, into_scott);
make_trait!(IntoParigot, into_parigot);
make_trait!(IntoStumpFu, into_stumpfu);

impl IntoChurch for usize {
    fn into_church(self) -> Term {
        let mut ret = Var(1);

        for _ in 0..self {
            ret = app(Var(2), ret);
        }

        abs!(2, ret)
    }
}

impl IntoScott for usize {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for _ in 0..self {
            ret = abs!(2, app(Var(1), ret));
        }

        ret
    }
}

impl IntoParigot for usize {
    fn into_parigot(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for _ in 0..self {
            ret = abs!(2, app!(Var(2), ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}

impl IntoStumpFu for usize {
    fn into_stumpfu(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for n in 1..self+1 {
            ret = abs!(2, app!(Var(2), n.into_church(), ret));
        }

        ret
    }
}

macro_rules! impl_pair {
    ($trait_name:ident, $function_name:ident) => (
        impl<T, U> $trait_name for (T, U) where T: $trait_name, U: $trait_name {
            fn $function_name(self) -> Term {
                abs(app!(Var(1), (self.0).$function_name(), (self.1).$function_name()))
            }
        }
    );
}

impl_pair!(IntoChurch, into_church);
impl_pair!(IntoScott, into_scott);
impl_pair!(IntoParigot, into_parigot);
impl_pair!(IntoStumpFu, into_stumpfu);

macro_rules! impl_list {
    ($trait_name:ident, $function_name:ident) => (
        impl<T> $trait_name for Vec<T> where T: $trait_name {
            fn $function_name(self) -> Term {
                let mut ret = abs!(2, Var(1));

                for term in self.into_iter().rev() {
                    ret = abs(app!(Var(1), term.$function_name(), ret))
                }

                ret
            }
        }
    );
}

impl_list!(IntoChurch, into_church);
impl_list!(IntoScott, into_scott);
impl_list!(IntoParigot, into_parigot);
impl_list!(IntoStumpFu, into_stumpfu);

macro_rules! impl_option {
    ($trait_name:ident, $function_name:ident) => (
        impl<T> $trait_name for Option<T> where T: $trait_name {
            fn $function_name(self) -> Term {
                match self {
                    None => abs!(2, Var(2)),
                    Some(value) => abs!(2, app(Var(1), value.$function_name()))
                }
            }
        }
    );
}

impl_option!(IntoChurch, into_church);
impl_option!(IntoScott, into_scott);
impl_option!(IntoParigot, into_parigot);
impl_option!(IntoStumpFu, into_stumpfu);
