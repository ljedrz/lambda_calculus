#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::stumpfu::numerals::*;
use lambda::*;

#[bench]
fn stumpfu_succ(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into_stumpfu()), HAP, 0) } );
}

#[bench]
fn stumpfu_add(b: &mut Bencher) {
    b.iter(|| { beta(app!(add(), 2.into_stumpfu(), 2.into_stumpfu()), HAP, 0) } );
}
