//! Conversions to different `Term` encodings

#![allow(missing_docs)]

use term::{Term, abs, app};
use term::Term::*;
use data::boolean::{fls, tru};

macro_rules! make_trait {
    ($trait_name:ident, $function_name:ident) => (
        pub trait $trait_name {
            #[doc="Performs the conversion."]
            fn $function_name(self) -> Term;
        }
    );
}

make_trait!(IntoChurch, into_church);

impl IntoChurch for usize {
    fn into_church(self) -> Term {
        let mut ret = Var(1);

        for _ in 0..self {
            ret = app(Var(2), ret);
        }

        abs!(2, ret)
    }
}

impl<T, U> IntoChurch for (T, U) where T: IntoChurch, U: IntoChurch {
    fn into_church(self) -> Term {
        abs(app!(Var(1), self.0.into_church(), self.1.into_church()))
    }
}

impl<T> IntoChurch for Vec<T> where T: IntoChurch {
    fn into_church(self) -> Term {
        let mut ret = fls();

        for term in self.into_iter().rev() {
            ret = abs(app!(Var(1), term.into_church(), ret))
        }

        ret
    }
}

impl<T> IntoChurch for Option<T> where T: IntoChurch {
    fn into_church(self) -> Term {
        match self {
            None => tru(),
            Some(value) => abs!(2, app(Var(1), value.into_church()))
        }
    }
}

make_trait!(IntoScott, into_scott);

impl IntoScott for usize {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for _ in 0..self {
            ret = abs!(2, app(Var(1), ret));
        }

        ret
    }
}

make_trait!(IntoParigot, into_parigot);

impl IntoParigot for usize {
    fn into_parigot(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for _ in 0..self {
            ret = abs!(2, app!(Var(2), ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}

make_trait!(IntoStumpFu, into_stumpfu);

impl IntoStumpFu for usize {
    fn into_stumpfu(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for n in 1..self+1 {
            ret = abs!(2, app!(Var(2), n.into_church(), ret));
        }

        ret
    }
}
