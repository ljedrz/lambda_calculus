#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::term::*;

#[bench]
fn term_is_supercombinator(b: &mut Bencher) {
    // Large arbitrary lambda term that is a supercombinator
    let big_term = abs!(1000, app!(
        abs!(1000, app!(abs(Var(10)), abs(Var(10)), abs(Var(10)))),
        abs!(2000, app!(abs(Var(20)), abs(Var(20)), abs(Var(20)))),
        abs!(3000, app!(abs(Var(30)), abs(Var(30)), abs(Var(30)))),
        abs!(4000, app!(abs(Var(40)), abs(Var(40)), abs(Var(40)))),
        abs!(5000, app!(abs(Var(50)), abs(Var(50)), abs(Var(50)))),
        abs!(6000, app!(abs(Var(60)), abs(Var(60)), abs(Var(60))))
    ));
    b.iter(|| { assert_eq!(big_term.is_supercombinator(), true) });
}
