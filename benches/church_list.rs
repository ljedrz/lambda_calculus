#![cfg(feature = "church")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::church::list::*;
use lambda::church::numerals::*;
use lambda::church::boolean::fls;
use lambda::combinators::C;
use lambda::*;

fn list1() -> Term { Term::from(vec![1.into()]) }
fn list2() -> Term { Term::from(vec![2.into(), 3.into()]) }
fn list3() -> Term { Term::from(vec![1.into(), 2.into(), 3.into()]) }
fn   gt1() -> Term { app!(C(), gt(), 1.into()) }

#[bench]
fn bench_null(b: &mut Bencher) {
    b.iter(|| { beta(app(null(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_head(b: &mut Bencher) {
    b.iter(|| { beta(app(head(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_tail(b: &mut Bencher) {
    b.iter(|| { beta(app(tail(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_length(b: &mut Bencher) {
    b.iter(|| { beta(app(length(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_list(b: &mut Bencher) {
    b.iter(|| { beta(app!(list(), 3.into(), 1.into(), 2.into(), 3.into()), HAP, 0, false) } );
}

#[bench]
fn bench_reverse(b: &mut Bencher) {
    b.iter(|| { beta(app(reverse(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_append(b: &mut Bencher) {
    b.iter(|| { beta(app!(append(), list1(), list2()), HAP, 0, false) } );
}

#[bench]
fn bench_index(b: &mut Bencher) {
    b.iter(|| { beta(app!(index(), 1.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_map(b: &mut Bencher) {
    b.iter(|| { beta(app!(map(), gt1(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_foldl(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldl(), plus(), 0.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_foldr(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldr(), plus(), 0.into(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_filter(b: &mut Bencher) {
    b.iter(|| { beta(app!(filter(), gt1(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_init(b: &mut Bencher) {
    b.iter(|| { beta(app(init(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_last(b: &mut Bencher) {
    b.iter(|| { beta(app(last(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_zip(b: &mut Bencher) {
    b.iter(|| { beta(app!(zip(), list3(), list3()), HAP, 0, false) } );
}

#[bench]
fn bench_zip_with(b: &mut Bencher) {
    b.iter(|| { beta(app!(zip_with(), fls(), list3(), list3()), HAP, 0, false) } );
}
