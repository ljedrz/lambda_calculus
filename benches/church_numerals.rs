#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::data::numerals::church::*;
use lambda::*;

macro_rules! bench_num {
    ($name:ident, $conversion:ident, $function:ident, $order:expr, $($n:expr),+) => (
        #[bench]
        fn $name(b: &mut Bencher) {
            b.iter(|| { beta(app!($function(), $($n.$conversion()),*), $order, 0) } );
        }
    );
}

bench_num!(church_succ, into_church, succ, HAP, 1);
bench_num!(church_pred, into_church, pred, HAP, 1);
bench_num!(church_add,  into_church, add,  HAP, 2, 2);
bench_num!(church_sub,  into_church, sub,  HAP, 2, 2);
bench_num!(church_mult, into_church, mult, HAP, 2, 2);
bench_num!(church_pow,  into_church, pow,  HAP, 2, 2);
bench_num!(church_div,  into_church, div,  HAP, 2, 2);
bench_num!(church_quot, into_church, quot, HAP, 2, 2);
bench_num!(church_rem,  into_church, rem,  HAP, 2, 2);
bench_num!(church_eq,   into_church, eq,   HAP, 2, 2);
bench_num!(church_neq,  into_church, neq,  HAP, 2, 2);
bench_num!(church_gt,   into_church, gt,   HAP, 2, 2);
bench_num!(church_lt,   into_church, lt,   HAP, 2, 2);
bench_num!(church_geq,  into_church, geq,  HAP, 2, 2);
bench_num!(church_leq,  into_church, leq,  HAP, 2, 2);
bench_num!(church_min,  into_church, min,  HAP, 2, 2);
bench_num!(church_max,  into_church, max,  HAP, 2, 2);
bench_num!(church_lshift, into_church, lshift,  HAP, 2, 2);
bench_num!(church_rshift, into_church, rshift,  HAP, 2, 2);
bench_num!(church_fac,   into_church, fac, HAP, 3);
