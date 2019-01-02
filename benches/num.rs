#![cfg(feature = "encoding")]

#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::data::num::{church, scott, parigot, stumpfu, binary};
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
bench_num!(binary,  binary_succ,  into_binary,  succ, HAP, 1);

bench_num!(church,  church_pred,  into_church,  pred, HAP, 1);
bench_num!(scott,   scott_pred,   into_scott,   pred, HAP, 1);
bench_num!(parigot, parigot_pred, into_parigot, pred, HAP, 1);
bench_num!(stumpfu, stumpfu_pred, into_stumpfu, pred, HAP, 1);
bench_num!(binary,  binary_pred,  into_binary,  pred, HAP, 1);

bench_num!(church,  church_add,  into_church,  add, HAP, 2, 2);
bench_num!(scott,   scott_add,   into_scott,   add, HNO, 2, 2);
bench_num!(parigot, parigot_add, into_parigot, add, HAP, 2, 2);
bench_num!(stumpfu, stumpfu_add, into_stumpfu, add, HAP, 2, 2);

bench_num!(church,  church_sub,  into_church,  sub, HAP, 2, 2);
//bench_num!(scott,   scott_sub,   into_scott,  sub, HAP, 2, 2);
bench_num!(parigot, parigot_sub, into_parigot, sub, HAP, 2, 2);
//bench_num!(stumpfu, stumpfu_sub, into_stumpfu, sub, HAP, 2, 2);

bench_num!(church,  church_mul,  into_church,  mul, HAP, 2, 2);
bench_num!(scott,   scott_mul,   into_scott,   mul, HNO, 2, 2);
bench_num!(parigot, parigot_mul, into_parigot, mul, HAP, 2, 2);
//bench_num!(stumpfu, stumpfu_mul, into_stumpfu, mul, HAP, 2, 2);

bench_num!(church, church_pow,  into_church, pow,  HAP, 2, 2);
bench_num!(scott,  scott_pow,   into_scott,  pow,  HNO, 2, 2);

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
bench_num!(church, church_is_even, into_church, is_even, HAP, 2);
bench_num!(church, church_is_odd,  into_church, is_odd,  HAP, 2);
bench_num!(church, church_shl, into_church, shl, HAP, 2, 2);
bench_num!(church, church_shr, into_church, shr, HAP, 2, 2);
bench_num!(church, church_fac, into_church, fac, HAP, 3);
