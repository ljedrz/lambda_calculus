#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::data::boolean::fls;
use lambda::data::list::pair::*;
use lambda::data::num::church::*;
use lambda::combinators::C;
use lambda::*;

fn list1() -> Term { vec![1.into_scott()].into_pair_list() }
fn list2() -> Term { vec![2.into_scott(), 3.into_scott()].into_pair_list() }
fn list3() -> Term { vec![1.into_scott(), 2.into_scott(), 3.into_scott()].into_pair_list() }
fn   gt1() -> Term { app!(C(), gt(), 1.into_scott()) }

#[bench]
fn pair_list_is_nil(b: &mut Bencher) {
    b.iter(|| { beta(app(is_nil(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_head(b: &mut Bencher) {
    b.iter(|| { beta(app(head(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_tail(b: &mut Bencher) {
    b.iter(|| { beta(app(tail(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_list(b: &mut Bencher) {
    b.iter(|| { beta(app!(list(), 3.into_church(), 1.into_church(), 2.into_church(), 3.into_church()), HAP, 0) } );
}

#[bench]
fn pair_list_reverse(b: &mut Bencher) {
    b.iter(|| { beta(app(reverse(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_append(b: &mut Bencher) {
    b.iter(|| { beta(app!(append(), list1(), list2()), HAP, 0) } );
}

#[bench]
fn pair_list_map(b: &mut Bencher) {
    b.iter(|| { beta(app!(map(), gt1(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_foldl(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldl(), add(), 0.into_church(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_foldr(b: &mut Bencher) {
    b.iter(|| { beta(app!(foldr(), add(), 0.into_church(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_filter(b: &mut Bencher) {
    b.iter(|| { beta(app!(filter(), gt1(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_init(b: &mut Bencher) {
    b.iter(|| { beta(app(init(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_last(b: &mut Bencher) {
    b.iter(|| { beta(app(last(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_zip(b: &mut Bencher) {
    b.iter(|| { beta(app!(zip(), list3(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_zip_with(b: &mut Bencher) {
    b.iter(|| { beta(app!(zip_with(), fls(), list3(), list3()), HAP, 0) } );
}

#[bench]
fn pair_list_take_while(b: &mut Bencher) {
    b.iter(|| { beta(app!(take_while(), is_zero(), list3()), HAP, 0) } );
}
