#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::*;
use lambda::data::list::{church, scott, parigot};

macro_rules! test_list {
    ($enc:ident, $name:ident, $fun:ident, $conv:ident) => (
        #[bench]
        fn $name(b: &mut Bencher) {
            b.iter(|| { beta(app!($enc::$fun(), vec![1.into_scott(), 2.into_scott(), 3.into_scott()].$conv()), HAP, 0) } );
        }
    );
}

test_list!( church,  church_head, head, into_church);
test_list!(  scott,   scott_head, head, into_scott);
test_list!(parigot, parigot_head, head, into_parigot);

test_list!( church,  church_tail, tail, into_church);
test_list!(  scott,   scott_tail, tail, into_scott);
test_list!(parigot, parigot_tail, tail, into_parigot);
