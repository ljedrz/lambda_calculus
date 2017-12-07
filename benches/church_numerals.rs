#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::reduction::*;
use lambda::church::numerals::*;

#[bench]
fn successor(b: &mut Bencher) {
    b.iter(|| { beta(app!(succ(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn predecessor(b: &mut Bencher) {
    b.iter(|| { beta(app!(pred(), 1.into()), HAP, 0, false) } );
}

#[bench]
fn subtraction(b: &mut Bencher) {
    b.iter(|| { beta(app!(sub(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn addition(b: &mut Bencher) {
    b.iter(|| { beta(app!(plus(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn multiplication(b: &mut Bencher) {
    b.iter(|| { beta(app!(mult(), 2.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn exponentiation(b: &mut Bencher) {
    b.iter(|| { beta(app!(pow(), 2.into(), 2.into()), NOR, 0, false) } );
}

#[bench]
fn division(b: &mut Bencher) {
    b.iter(|| { beta(app!(div(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn quotient(b: &mut Bencher) {
    b.iter(|| { beta(app!(quot(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn remainder(b: &mut Bencher) {
    b.iter(|| { beta(app!(rem(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_eq(b: &mut Bencher) {
    b.iter(|| { beta(app!(eq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_neq(b: &mut Bencher) {
    b.iter(|| { beta(app!(neq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_gt(b: &mut Bencher) {
    b.iter(|| { beta(app!(gt(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_lt(b: &mut Bencher) {
    b.iter(|| { beta(app!(lt(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_geq(b: &mut Bencher) {
    b.iter(|| { beta(app!(geq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn compare_leq(b: &mut Bencher) {
    b.iter(|| { beta(app!(leq(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn minimum(b: &mut Bencher) {
    b.iter(|| { beta(app!(min(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn maximum(b: &mut Bencher) {
    b.iter(|| { beta(app!(max(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn left_shift(b: &mut Bencher) {
    b.iter(|| { beta(app!(lshift(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn right_shift(b: &mut Bencher) {
    b.iter(|| { beta(app!(rshift(), 3.into(), 2.into()), HAP, 0, false) } );
}

#[bench]
fn factorial(b: &mut Bencher) {
    b.iter(|| { beta(app!(fac(), 3.into()), HAP, 0, false) } );
}
