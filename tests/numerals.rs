#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::numerals::{church, scott, parigot, stumpfu};

macro_rules! test_num {
    ($encoding:ident, $name:ident, $conversion:ident, $function:ident, $($($n:expr),+ => $result:expr),+) => (
        #[test]
        fn $name() {
            $(assert_eq!(beta(app!($encoding::$function(), $($n.$conversion()),*), HNO, 0), $result.$conversion());)*
        }
    );
}

test_num!(church,  church_succ,  into_church,  succ, 0 => 1, 1 => 2, 2 => 3);
test_num!(scott,   scott_succ,   into_scott,   succ, 0 => 1, 1 => 2, 2 => 3);
test_num!(parigot, parigot_succ, into_parigot, succ, 0 => 1, 1 => 2, 2 => 3);
test_num!(stumpfu, stumpfu_succ, into_stumpfu, succ, 0 => 1, 1 => 2, 2 => 3);

test_num!(church,  church_pred,  into_church,  pred, 1 => 0, 2 => 1, 3 => 2);
test_num!(scott,   scott_pred,   into_scott,   pred, 1 => 0, 2 => 1, 3 => 2);
test_num!(parigot, parigot_pred, into_parigot, pred, 1 => 0, 2 => 1, 3 => 2);
test_num!(stumpfu, stumpfu_pred, into_stumpfu, pred, 1 => 0, 2 => 1, 3 => 2);

test_num!(church,  church_add,  into_church,  add, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 2, 3 => 5);
test_num!(scott,   scott_add,   into_scott,   add, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 2, 3 => 5);
test_num!(parigot, parigot_add, into_parigot, add, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 2, 3 => 5);
test_num!(stumpfu, stumpfu_add, into_stumpfu, add, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 2, 3 => 5);

test_num!(church,  church_sub,  into_church,  sub, 0, 0 => 0, 0, 1 => 0, 1, 0 => 1, 3, 2 => 1);
//test_num!(scott,  scott_sub,  into_scott,  sub, 0, 0 => 0, 0, 1 => 0, 1, 0 => 1, 3, 2 => 1);
test_num!(parigot, parigot_sub, into_parigot, sub, 0, 0 => 0, 0, 1 => 0, 1, 0 => 1, 3, 2 => 1);
//test_num!(stumpfu, stumpfu_sub, into_stumpfu, sub, 0, 0 => 0, 0, 1 => 0, 1, 0 => 1, 3, 2 => 1);

test_num!(church,  church_mul,  into_church,  mul, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 3, 2 => 6);
test_num!(scott,   scott_mul,   into_scott,   mul, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 3, 2 => 6);
test_num!(parigot, parigot_mul, into_parigot, mul, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 3, 2 => 6);
//test_num!(stumpfu, stumpfu_mul, into_stumpfu, mul, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 3, 2 => 6);

test_num!(church,  church_pow,  into_church,  pow, 0, 0 => 1, 0, 1 => 0, 1, 0 => 1, 1, 3 => 1, 2, 4 => 16);
test_num!(scott,   scott_pow,   into_scott,   pow, 0, 0 => 1, 0, 1 => 0, 1, 0 => 1, 1, 3 => 1, 2, 4 => 16);
//test_num!(parigot, parigot_pow, into_parigot, pow, 0, 0 => 1, 0, 1 => 0, 1, 0 => 1, 1, 3 => 1, 2, 4 => 16);
//test_num!(stumpfu, stumpfu_pow, into_stumpfu, pow, 0, 0 => 1, 0, 1 => 0, 1, 0 => 1, 1, 3 => 1, 2, 4 => 16);

test_num!(church,  church_div,  into_church,  div, 0, 1 => (0, 0), 2, 1 => (2, 0), 1, 2 => (0, 1), 5, 2 => (2, 1));
//test_num!(scott,   scott_div,   into_scott,   div, 0, 1 => (0, 0), 2, 1 => (2, 0), 1, 2 => (0, 1), 5, 2 => (2, 1));
//test_num!(parigot, parigot_div, into_parigot, div, 0, 1 => (0, 0), 2, 1 => (2, 0), 1, 2 => (0, 1), 5, 2 => (2, 1));
//test_num!(stumpfu, stumpfu_div, into_stumpfu, div, 0, 1 => (0, 0), 2, 1 => (2, 0), 1, 2 => (0, 1), 5, 2 => (2, 1));

test_num!(church,  church_quot,  into_church,  quot, 0, 1 => 0, 2, 1 => 2, 3, 2 => 1, 5, 2 => 2);
//test_num!(scott,   scott_quot,   into_scott,   quot, 0, 1 => 0, 2, 1 => 2, 3, 2 => 1, 5, 2 => 2);
//test_num!(parigot, parigot_quot, into_parigot, quot, 0, 1 => 0, 2, 1 => 2, 3, 2 => 1, 5, 2 => 2);
//test_num!(stumpfu, stumpfu_quot, into_stumpfu, quot, 0, 1 => 0, 2, 1 => 2, 3, 2 => 1, 5, 2 => 2);

test_num!(church,  church_rem,  into_church,  rem, 0, 1 => 0, 2, 1 => 0, 3, 2 => 1, 5, 2 => 1);
//test_num!(scott,   scott_rem,   into_scott,   rem, 0, 1 => 0, 2, 1 => 0, 3, 2 => 1, 5, 2 => 1);
//test_num!(parigot, parigot_rem, into_parigot, rem, 0, 1 => 0, 2, 1 => 0, 3, 2 => 1, 5, 2 => 1);
//test_num!(stumpfu, stumpfu_rem, into_stumpfu, rem, 0, 1 => 0, 2, 1 => 0, 3, 2 => 1, 5, 2 => 1);

test_num!(church,  church_min,  into_church,  min, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 1, 2 => 1);
//test_num!(scott,   scott_min,   into_scott,   min, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 1, 2 => 1);
//test_num!(parigot, parigot_min, into_parigot, min, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 1, 2 => 1);
//test_num!(stumpfu, stumpfu_min, into_stumpfu, min, 0, 0 => 0, 0, 1 => 0, 1, 0 => 0, 1, 2 => 1);

test_num!(church,  church_max,  into_church,  max, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 1, 2 => 2);
//test_num!(scott,   scott_max,   into_scott,   max, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 1, 2 => 2);
//test_num!(parigot, parigot_max, into_parigot, max, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 1, 2 => 2);
//test_num!(stumpfu, stumpfu_max, into_stumpfu, max, 0, 0 => 0, 0, 1 => 1, 1, 0 => 1, 1, 2 => 2);

test_num!(church,  church_lshift,  into_church,  lshift, 0, 2 => 0, 1, 0 => 1, 2, 0 => 2, 2, 2 => 8, 3, 2 => 12, 2, 3 => 16, 5, 1 => 10);
//test_num!(scott,   scott_lshift,   into_scott,   lshift, 0, 2 => 0, 1, 0 => 0, 2, 0 => 2, 2, 2 => 8, 3, 2 => 12, 2, 3 => 16, 5, 1 => 10);
//test_num!(parigot, parigot_lshift, into_parigot, lshift, 0, 2 => 0, 1, 0 => 0, 2, 0 => 2, 2, 2 => 8, 3, 2 => 12, 2, 3 => 16, 5, 1 => 10);
//test_num!(stumpfu, stumpfu_lshift, into_stumpfu, lshift, 0, 2 => 0, 1, 0 => 0, 2, 0 => 2, 2, 2 => 8, 3, 2 => 12, 2, 3 => 16, 5, 1 => 10);

test_num!(church,  church_rshift,  into_church,  rshift, 1, 0 => 1, 2, 0 => 2, 2, 1 => 1, 2, 2 => 0, 5, 1 => 2, 9, 1 => 4, 7, 1 => 3);
//test_num!(scott,   scott_rshift,   into_scott,   rshift, 1, 0 => 1, 2, 0 => 2, 2, 1 => 1, 2, 2 => 0, 5, 1 => 2, 9, 1 => 4, 7, 1 => 3);
//test_num!(parigot, parigot_rshift, into_parigot, rshift, 1, 0 => 1, 2, 0 => 2, 2, 1 => 1, 2, 2 => 0, 5, 1 => 2, 9, 1 => 4, 7, 1 => 3);
//test_num!(stumpfu, stumpfu_rshift, into_stumpfu, rshift, 1, 0 => 1, 2, 0 => 2, 2, 1 => 1, 2, 2 => 0, 5, 1 => 2, 9, 1 => 4, 7, 1 => 3);

test_num!(church,  church_fac,  into_church,  fac, 0 => 1, 1 => 1, 2 => 2, 3 => 6);
//test_num!(scott,   scott_fac,   into_scott,   fac, 0 => 1, 1 => 1, 2 => 2, 3 => 6);
//test_num!(parigot, parigot_fac, into_parigot, fac, 0 => 1, 1 => 1, 2 => 2, 3 => 6);
//test_num!(stumpfu, stumpfu_fac, into_stumpfu, fac, 0 => 1, 1 => 1, 2 => 2, 3 => 6);
