//! Numeral encoding conversions

#![allow(missing_docs)]

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use self::Encoding::*;

/// The type of numeric encoding.
#[derive(Debug, Clone, Copy)]
pub enum Encoding {
    Church,
    Scott,
    Parigot,
    StumpFu,
    Binary
}

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
make_trait!(IntoBinaryNum, into_binary);

pub trait IntoSignedNum {
    #[doc="Performs the conversion. The supported `Encoding`s are `Church`, `Scott`, `Parigot` and
          `StumpFu`."]
    fn into_signed(self, encoding: Encoding) -> Term;
}


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

impl IntoBinaryNum for usize {
    fn into_binary(self) -> Term {
        let mut ret = Var(3);

        if self != 0 {
            let binstr = format!("{:b}", self).into_bytes();

            for bit in binstr {
                if bit == b'0' {
                    ret = app(Var(2), ret);
                } else {
                    ret = app(Var(1), ret);
                }
            }
        }

        abs!(3, ret)
    }
}

impl IntoSignedNum for i32 {
    fn into_signed(self, encoding: Encoding) -> Term {
        let modulus = self.abs() as usize;

        let numeral = match encoding {
            Church  => modulus.into_church(),
            Scott   => modulus.into_scott(),
            Parigot => modulus.into_parigot(),
            StumpFu => modulus.into_stumpfu(),
            Binary  => panic!("signed binary numbers are not supported")
        };

        if self > 0 {
            tuple!(numeral, abs!(2, Var(1)))
        } else {
            tuple!(abs!(2, Var(1)), numeral)
        }
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
impl_pair!(IntoBinaryNum, into_binary);

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
impl_option!(IntoBinaryNum, into_binary);

macro_rules! impl_result {
    ($trait_name:ident, $function_name:ident) => (
        impl<T, U> $trait_name for Result<T, U> where T: $trait_name, U: $trait_name {
            fn $function_name(self) -> Term {
                match self {
                    Ok(ok) => abs!(2, app(Var(2), ok.$function_name())),
                    Err(err) => abs!(2, app(Var(1), err.$function_name()))
                }
            }
        }
    );
}

impl_result!(IntoChurchNum, into_church);
impl_result!(IntoScottNum, into_scott);
impl_result!(IntoParigotNum, into_parigot);
impl_result!(IntoStumpFuNum, into_stumpfu);
impl_result!(IntoBinaryNum, into_binary);
