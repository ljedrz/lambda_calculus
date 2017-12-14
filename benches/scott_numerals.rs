#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::scott::numerals::*;
use lambda::*;

#[bench]
fn scott_succ(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into_scott()), HAP, 0) } );
}

#[bench]
fn scott_pred(b: &mut Bencher) {
    b.iter(|| { beta(app!(pred(), 1.into_scott()), HAP, 0) } );
}
