//! List encoding conversions

#![allow(missing_docs)]

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::num::convert::*;

macro_rules! make_trait {
    ($trait_name:ident, $function_name:ident) => (
        pub trait $trait_name {
            #[doc="Performs the conversion."]
            fn $function_name(self) -> Term;
        }
    );
}

make_trait!(IntoPairList, into_pair_list);
make_trait!(IntoChurchList, into_church);
make_trait!(IntoScottList, into_scott);
make_trait!(IntoParigotList, into_parigot);

impl IntoPairList for Vec<Term> {
    fn into_pair_list(self) -> Term {
        let mut ret = abs!(2, Var(1));

        for t in self.into_iter().rev() {
            ret = abs(app!(Var(1), t, ret))
        }

        ret
    }
}

impl IntoChurchList for Vec<Term> {
    fn into_church(self) -> Term {
        let mut ret = Var(2);

        for t in self.into_iter().rev() {
            ret = app!(Var(1), t, ret);
        }

        abs!(2, ret)
    }
}

impl<T: IntoChurchNum> IntoChurchList for Vec<T> {
    fn into_church(self) -> Term {
        self.into_iter().map(|t| t.into_church()).collect::<Vec<Term>>().into_church()
    }
}

impl IntoScottList for Vec<Term> {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for t in self.into_iter().rev() {
            ret = abs!(2, app!(Var(1), t, ret));
        }

        ret
    }
}

impl<T: IntoScottNum> IntoScottList for Vec<T> {
    fn into_scott(self) -> Term {
        self.into_iter().map(|t| t.into_scott()).collect::<Vec<Term>>().into_scott()
    }
}

impl IntoParigotList for Vec<Term> {
    fn into_parigot(self) -> Term {
        let mut ret  = abs!(2, Var(2));

        for t in self.into_iter().rev() {
            ret = abs!(2, app!(Var(1), t, ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}

impl<T: IntoParigotNum> IntoParigotList for Vec<T> {
    fn into_parigot(self) -> Term {
        self.into_iter().map(|t| t.into_parigot()).collect::<Vec<Term>>().into_parigot()
    }
}
