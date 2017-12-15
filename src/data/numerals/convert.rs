//! Conversions to different `Term` encodings

#![allow(missing_docs)]

use term::Term;

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
