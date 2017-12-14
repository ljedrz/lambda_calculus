#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::numerals::*;
use lambda::combinators::C;

#[test]
fn church_succ() {
    assert_eq!(beta(app!(succ(), 0.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(succ(), 1.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(succ(), 2.into_church()), HAP, 0), 3.into_church());
}

#[test]
fn church_pred() {
    assert_eq!(beta(app!(pred(), 0.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(pred(), 1.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(pred(), 5.into_church()), HAP, 0), 4.into_church());
}

#[test]
fn church_add_sub() {
    assert_eq!(beta(app!(     add(), 1.into_church()), HAP, 0), succ());
    assert_eq!(beta(app!(C(), sub(), 1.into_church()), HAP, 0), pred());
}

#[test]
fn church_mult() {
    assert_eq!(beta(app!(mult(), 3.into_church(), 4.into_church()), HAP, 0), 12.into_church());
    assert_eq!(beta(app!(mult(), 1.into_church(), 3.into_church()), HAP, 0),  3.into_church());
    assert_eq!(beta(app!(mult(), 3.into_church(), 1.into_church()), HAP, 0),  3.into_church());
    assert_eq!(beta(app!(mult(), 5.into_church(), 0.into_church()), HAP, 0),  0.into_church());
    assert_eq!(beta(app!(mult(), 0.into_church(), 5.into_church()), HAP, 0),  0.into_church());
}

#[test]
fn church_pow() {
    assert_eq!(beta(app!(pow(), 2.into_church(), 4.into_church()), HAP, 0), 16.into_church());
    assert_eq!(beta(app!(pow(), 1.into_church(), 3.into_church()), HAP, 0),  1.into_church());
    assert_eq!(beta(app!(pow(), 3.into_church(), 1.into_church()), HAP, 0),  3.into_church());
    assert_eq!(beta(app!(pow(), 5.into_church(), 0.into_church()), HAP, 0),  1.into_church());
    assert_eq!(beta(app!(pow(), 0.into_church(), 5.into_church()), HAP, 0),  0.into_church());
}

#[test]
fn church_div() {
    assert_eq!(beta(app!(div(), 2.into_church(), 2.into_church()), HAP, 0), (1.into_church(), 0.into_church()).into_church());
    assert_eq!(beta(app!(div(), 3.into_church(), 2.into_church()), HAP, 0), (1.into_church(), 1.into_church()).into_church());
    assert_eq!(beta(app!(div(), 5.into_church(), 2.into_church()), HAP, 0), (2.into_church(), 1.into_church()).into_church());
    assert_eq!(beta(app!(div(), 2.into_church(), 1.into_church()), HAP, 0), (2.into_church(), 0.into_church()).into_church());
    assert_eq!(beta(app!(div(), 0.into_church(), 3.into_church()), HAP, 0), (0.into_church(), 0.into_church()).into_church());
}

#[test]
fn church_quot() {
    assert_eq!(beta(app!(quot(), 2.into_church(), 2.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(quot(), 3.into_church(), 2.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(quot(), 5.into_church(), 2.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(quot(), 2.into_church(), 1.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(quot(), 0.into_church(), 3.into_church()), HAP, 0), 0.into_church());
}

#[test]
fn church_rem() {
    assert_eq!(beta(app!(rem(), 2.into_church(), 2.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(rem(), 3.into_church(), 2.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(rem(), 2.into_church(), 5.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(rem(), 2.into_church(), 1.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(rem(), 0.into_church(), 3.into_church()), HAP, 0), 0.into_church());
}

#[test]
fn church_fac() {
    assert_eq!(beta(app!(fac(), 0.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(fac(), 1.into_church()), HAP, 0), 1.into_church());
    assert_eq!(beta(app!(fac(), 2.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(fac(), 3.into_church()), HAP, 0), 6.into_church());
}

#[test]
fn church_min() {
    assert_eq!(beta(app!(min(), 0.into_church(), 0.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(min(), 4.into_church(), 4.into_church()), HAP, 0), 4.into_church());
    assert_eq!(beta(app!(min(), 2.into_church(), 3.into_church()), HAP, 0), 2.into_church());
    assert_eq!(beta(app!(min(), 5.into_church(), 3.into_church()), HAP, 0), 3.into_church());
    assert_eq!(beta(app!(min(), 0.into_church(), 1.into_church()), HAP, 0), 0.into_church());
}

#[test]
fn church_max() {
    assert_eq!(beta(app!(max(), 0.into_church(), 0.into_church()), HAP, 0), 0.into_church());
    assert_eq!(beta(app!(max(), 4.into_church(), 4.into_church()), HAP, 0), 4.into_church());
    assert_eq!(beta(app!(max(), 2.into_church(), 3.into_church()), HAP, 0), 3.into_church());
    assert_eq!(beta(app!(max(), 5.into_church(), 3.into_church()), HAP, 0), 5.into_church());
    assert_eq!(beta(app!(max(), 0.into_church(), 1.into_church()), HAP, 0), 1.into_church());
}

#[test]
fn church_lshift() {
     assert_eq!(beta(app!(lshift(), 0.into_church(), 2.into_church()), HAP, 0), 0.into_church());
     assert_eq!(beta(app!(lshift(), 1.into_church(), 0.into_church()), HAP, 0), 1.into_church());
     assert_eq!(beta(app!(lshift(), 2.into_church(), 0.into_church()), HAP, 0), 2.into_church());
     assert_eq!(beta(app!(lshift(), 2.into_church(), 2.into_church()), HAP, 0), 8.into_church());
     assert_eq!(beta(app!(lshift(), 3.into_church(), 2.into_church()), HAP, 0), 12.into_church());
     assert_eq!(beta(app!(lshift(), 2.into_church(), 3.into_church()), HAP, 0), 16.into_church());
     assert_eq!(beta(app!(lshift(), 5.into_church(), 1.into_church()), HAP, 0), 10.into_church());
}

#[test]
fn church_rshift() {
     assert_eq!(beta(app!(rshift(), 1.into_church(), 0.into_church()), HAP, 0), 1.into_church());
     assert_eq!(beta(app!(rshift(), 2.into_church(), 0.into_church()), HAP, 0), 2.into_church());
     assert_eq!(beta(app!(rshift(), 0.into_church(), 2.into_church()), HAP, 0), 0.into_church());
     assert_eq!(beta(app!(rshift(), 2.into_church(), 1.into_church()), HAP, 0), 1.into_church());
     assert_eq!(beta(app!(rshift(), 2.into_church(), 2.into_church()), HAP, 0), 0.into_church());
     assert_eq!(beta(app!(rshift(), 5.into_church(), 1.into_church()), HAP, 0), 2.into_church());
     assert_eq!(beta(app!(rshift(), 9.into_church(), 1.into_church()), HAP, 0), 4.into_church());
     assert_eq!(beta(app!(rshift(), 9.into_church(), 2.into_church()), HAP, 0), 2.into_church());
     assert_eq!(beta(app!(rshift(), 7.into_church(), 1.into_church()), HAP, 0), 3.into_church());
}

#[test]
fn church_is_even() {
     assert_eq!(beta(app!(is_even(), 0.into_church()), HAP, 0), true.into_church());
     assert_eq!(beta(app!(is_even(), 1.into_church()), HAP, 0), false.into_church());
     assert_eq!(beta(app!(is_even(), 2.into_church()), HAP, 0), true.into_church());
     assert_eq!(beta(app!(is_even(), 8.into_church()), HAP, 0), true.into_church());
     assert_eq!(beta(app!(is_even(), 9.into_church()), HAP, 0), false.into_church());
}

#[test]
fn church_is_odd() {
     assert_eq!(beta(app!(is_odd(), 0.into_church()), HAP, 0), false.into_church());
     assert_eq!(beta(app!(is_odd(), 1.into_church()), HAP, 0), true.into_church());
     assert_eq!(beta(app!(is_odd(), 2.into_church()), HAP, 0), false.into_church());
     assert_eq!(beta(app!(is_odd(), 8.into_church()), HAP, 0), false.into_church());
     assert_eq!(beta(app!(is_odd(), 9.into_church()), HAP, 0), true.into_church());
}
