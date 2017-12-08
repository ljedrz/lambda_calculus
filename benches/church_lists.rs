#![cfg(not(feature = "no_church"))]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::church::lists::*;
use lambda::church::numerals::*;
use lambda::combinators::c;
use lambda::*;

fn list1() -> Term { Term::from(vec![1.into()]) }
fn list2() -> Term { Term::from(vec![2.into(), 3.into()]) }
fn list3() -> Term { Term::from(vec![1.into(), 2.into(), 3.into()]) }
fn   gt1() -> Term { app!(c(), gt(), 1.into()) }

#[bench]
fn list_null(b: &mut Bencher) {
    b.iter(|| { beta(app(null(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_head(b: &mut Bencher) {
    b.iter(|| { beta(app(head(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_tail(b: &mut Bencher) {
    b.iter(|| { beta(app(tail(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_length(b: &mut Bencher) {
    b.iter(|| { beta(app(length(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_building(b: &mut Bencher) {
    b.iter(|| { beta(app!(list(), 3.into(), 1.into(), 2.into(), 3.into()), HAP, 0, false) } );
}

#[bench]
fn reversing(b: &mut Bencher) {
    b.iter(|| { beta(app(reverse(), list3()), HAP, 0, false) } );
}

#[bench]
fn appending(b: &mut Bencher) {
    b.iter(|| { beta(app!(append(), list1(), list2()), HAP, 0, false) } );
}

#[bench]
fn indexing(b: &mut Bencher) {
    b.iter(|| { beta(app!(index(), 1.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn mapping(b: &mut Bencher) {
    b.iter(|| { beta(app!(map(), gt1(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_foldl(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldl(), plus(), 0.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_foldr(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldr(), plus(), 0.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn filtering(b: &mut Bencher) {
    b.iter(|| { beta(app!(filter(), gt1(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_init(b: &mut Bencher) {
    b.iter(|| { beta(app(init(), list3()), HAP, 0, false) } );
}

#[bench]
fn list_last(b: &mut Bencher) {
    b.iter(|| { beta(app(last(), list3()), HAP, 0, false) } );
}
