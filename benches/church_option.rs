#![cfg(not(feature = "no_church"))]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::reduction::*;
use lambda::church::option::*;
use lambda::church::numerals::succ;

#[bench]
fn option_is_none(b: &mut Bencher) {
    b.iter(|| { beta(app!(is_none(), none()), HAP, 0, false) } );
}

#[bench]
fn option_is_some(b: &mut Bencher) {
    b.iter(|| { beta(app!(is_some(), none()), HAP, 0, false) } );
}

#[bench]
fn option_map_or(b: &mut Bencher) {
    b.iter(|| { beta(app!(map_or(), 0.into(), succ(), none()), HAP, 0, false) } );
}
