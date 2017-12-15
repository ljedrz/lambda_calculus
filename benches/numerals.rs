#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

#[macro_use]
extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::data::numerals::{church, scott, parigot, stumpfu};
use lambda::*;

macro_rules! bench_num {
    ($encoding:ident, $name:ident, $conversion:ident, $function:ident, $order:expr, $($n:expr),+) => (
        #[bench]
        fn $name(b: &mut Bencher) {
            b.iter(|| { beta(app!($encoding::$function(), $($n.$conversion()),*), $order, 0) } );
        }
    );
}

bench_num!(church,  church_succ,  into_church,  succ, HAP, 1);
bench_num!(scott,   scott_succ,   into_scott,   succ, HAP, 1);
bench_num!(parigot, parigot_succ, into_parigot, succ, HAP, 1);
bench_num!(stumpfu, stumpfu_succ, into_stumpfu, succ, HAP, 1);

bench_num!(church,  church_pred,  into_church,  pred, HAP, 1);
bench_num!(scott,   scott_pred,   into_scott,   pred, HAP, 1);
bench_num!(parigot, parigot_pred, into_parigot, pred, HAP, 1);
bench_num!(stumpfu, stumpfu_pred, into_stumpfu, pred, HAP, 1);

bench_num!(church,  church_add,  into_church,  add, HAP, 2, 2);
//bench_num!(scott,   scott_add,   into_scott,  add, HAP, 2, 2);
bench_num!(parigot, parigot_add, into_parigot, add, HAP, 2, 2);
bench_num!(stumpfu, stumpfu_add, into_stumpfu, add, HAP, 2, 2);

bench_num!(church,  church_sub,  into_church,  sub, HAP, 2, 2);
//bench_num!(scott,   scott_sub,   into_scott,  sub, HAP, 2, 2);
bench_num!(parigot, parigot_sub, into_parigot, sub, HAP, 2, 2);
//bench_num!(stumpfu, stumpfu_sub, into_stumpfu, sub, HAP, 2, 2);

bench_num!(church,  church_mult,  into_church,  mult, HAP, 2, 2);
//bench_num!(scott,   scott_mult,   into_scott,   mult, HAP, 2, 2);
bench_num!(parigot, parigot_mult, into_parigot, mult, HAP, 2, 2);
//bench_num!(stumpfu, stumpfu_mult, into_stumpfu, mult, HAP, 2, 2);

bench_num!(church, church_pow,  into_church, pow,  HAP, 2, 2);
bench_num!(church, church_div,  into_church, div,  HAP, 2, 2);
bench_num!(church, church_quot, into_church, quot, HAP, 2, 2);
bench_num!(church, church_rem,  into_church, rem,  HAP, 2, 2);
bench_num!(church, church_eq,   into_church, eq,   HAP, 2, 2);
bench_num!(church, church_neq,  into_church, neq,  HAP, 2, 2);
bench_num!(church, church_gt,   into_church, gt,   HAP, 2, 2);
bench_num!(church, church_lt,   into_church, lt,   HAP, 2, 2);
bench_num!(church, church_geq,  into_church, geq,  HAP, 2, 2);
bench_num!(church, church_leq,  into_church, leq,  HAP, 2, 2);
bench_num!(church, church_min,  into_church, min,  HAP, 2, 2);
bench_num!(church, church_max,  into_church, max,  HAP, 2, 2);
bench_num!(church, church_lshift, into_church, lshift,  HAP, 2, 2);
bench_num!(church, church_rshift, into_church, rshift,  HAP, 2, 2);
bench_num!(church, church_fac,   into_church, fac, HAP, 3);
