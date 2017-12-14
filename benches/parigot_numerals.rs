#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::parigot::numerals::*;
use lambda::*;

#[bench]
fn parigot_succ(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into_parigot()), HAP, 0) } );
}

#[bench]
fn parigot_pred(b: &mut Bencher) {
    b.iter(|| { beta(app!(pred(), 1.into_parigot()), HAP, 0) } );
}

#[bench]
fn parigot_add(b: &mut Bencher) {
    b.iter(|| { beta(app!(add(), 1.into_parigot(), 2.into_parigot()), HAP, 0) } );
}
