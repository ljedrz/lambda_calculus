//! Conversions to different numeral encodings

#![allow(missing_docs)]

use term::{Term, abs, app};
use term::Term::*;

macro_rules! make_trait {
    ($trait_name:ident, $function_name:ident) => (
        pub trait $trait_name {
            #[doc="Performs the conversion."]
            fn $function_name(self) -> Term;
        }
    );
}

make_trait!(IntoChurchNum, into_church);
make_trait!(IntoScottNum, into_scott);
make_trait!(IntoParigotNum, into_parigot);
make_trait!(IntoStumpFuNum, into_stumpfu);

impl IntoChurchNum for usize {
    fn into_church(self) -> Term {
        let mut ret = Var(1);

        for _ in 0..self {
            ret = app(Var(2), ret);
        }

        abs!(2, ret)
    }
}

impl IntoScottNum for usize {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for _ in 0..self {
            ret = abs!(2, app(Var(1), ret));
        }

        ret
    }
}

impl IntoParigotNum for usize {
    fn into_parigot(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for _ in 0..self {
            ret = abs!(2, app!(Var(2), ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}

impl IntoStumpFuNum for usize {
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

impl_pair!(IntoChurchNum, into_church);
impl_pair!(IntoScottNum, into_scott);
impl_pair!(IntoParigotNum, into_parigot);
impl_pair!(IntoStumpFuNum, into_stumpfu);

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

impl_option!(IntoChurchNum, into_church);
impl_option!(IntoScottNum, into_scott);
impl_option!(IntoParigotNum, into_parigot);
impl_option!(IntoStumpFuNum, into_stumpfu);
