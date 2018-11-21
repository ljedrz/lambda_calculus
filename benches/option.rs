#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::data::option::*;
use lambda::data::num::church::succ;
use lambda::*;

#[bench]
fn option_is_none(b: &mut Bencher) {
    b.iter(|| { beta(app!(is_none(), none()), HAP, 0) } );
}

#[bench]
fn option_is_some(b: &mut Bencher) {
    b.iter(|| { beta(app!(is_some(), none()), HAP, 0) } );
}

#[bench]
fn option_map_or(b: &mut Bencher) {
    b.iter(|| { beta(app!(map_or(), 0.into_church(), succ(), none()), HAP, 0) } );
}
