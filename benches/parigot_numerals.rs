#![cfg(feature = "parigot")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::reduction::*;
use lambda::parigot::numerals::*;

#[bench]
fn bench_succ(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn bench_pred(b: &mut Bencher) {
    b.iter(|| { beta(app!(pred(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn bench_plus(b: &mut Bencher) {
    b.iter(|| { beta(app!(plus(), 1.into(), 2.into()), HAP, 0, false) } );
}
