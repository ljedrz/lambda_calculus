//! Conversions to different `Term` encodings

#![allow(missing_docs)]

use term::{Term, abs, app};
use term::Term::*;

/// The encoding type applicable to numerals.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ListEncoding {
    /// Single pair encoding,
    Pair,
    /// Church encoding
    Church,
    /// Scott encoding
    Scott,
    /// Parigot encoding
    Parigot
}

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

impl IntoScottList for Vec<Term> {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for t in self.into_iter().rev() {
            ret = abs!(2, app!(Var(1), t, ret));
        }

        ret
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
