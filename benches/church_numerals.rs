#![cfg(feature = "church")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::reduction::*;
use lambda::church::numerals::*;

#[bench]
fn bench_succ(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn bench_pred(b: &mut Bencher) {
    b.iter(|| { beta(app!(pred(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn bench_sub(b: &mut Bencher) {
    b.iter(|| { beta(app!(sub(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_plus(b: &mut Bencher) {
    b.iter(|| { beta(app!(plus(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_mult(b: &mut Bencher) {
    b.iter(|| { beta(app!(mult(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_pow(b: &mut Bencher) {
    b.iter(|| { beta(app!(pow(), 2.into(), 2.into()), NOR, 0, false) } );
}

#[bench]
fn bench_div(b: &mut Bencher) {
    b.iter(|| { beta(app!(div(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_quot(b: &mut Bencher) {
    b.iter(|| { beta(app!(quot(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_rem(b: &mut Bencher) {
    b.iter(|| { beta(app!(rem(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_eq(b: &mut Bencher) {
    b.iter(|| { beta(app!(eq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_neq(b: &mut Bencher) {
    b.iter(|| { beta(app!(neq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_gt(b: &mut Bencher) {
    b.iter(|| { beta(app!(gt(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_lt(b: &mut Bencher) {
    b.iter(|| { beta(app!(lt(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_geq(b: &mut Bencher) {
    b.iter(|| { beta(app!(geq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_leq(b: &mut Bencher) {
    b.iter(|| { beta(app!(leq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_min(b: &mut Bencher) {
    b.iter(|| { beta(app!(min(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_max(b: &mut Bencher) {
    b.iter(|| { beta(app!(max(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_lshift(b: &mut Bencher) {
    b.iter(|| { beta(app!(lshift(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_rshift(b: &mut Bencher) {
    b.iter(|| { beta(app!(rshift(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn bench_fac(b: &mut Bencher) {
    b.iter(|| { beta(app!(fac(), 3.into()), HAP, 0, false) } );
}
