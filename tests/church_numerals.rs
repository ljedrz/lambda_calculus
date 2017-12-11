#![cfg(not(feature = "no_church"))]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::numerals::*;
use lambda::combinators::c;

#[test]
fn church_successor() {
    assert_eq!(beta(app!(succ(), 0.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(succ(), 1.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(succ(), 2.into()), HAP, 0, false), 3.into());
}

#[test]
fn church_predecessor() {
    assert_eq!(beta(app!(pred(), 0.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(pred(), 1.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(pred(), 5.into()), HAP, 0, false), 4.into());
}

#[test]
fn church_plus_sub_equivalents() {
    assert_eq!(beta(app!(    plus(), 1.into()), HAP, 0, false), succ());
    assert_eq!(beta(app!(c(), sub(), 1.into()), HAP, 0, false), pred());
}

#[test]
fn church_multiplication() {
    assert_eq!(beta(app!(mult(), 3.into(), 4.into()), HAP, 0, false), 12.into());
    assert_eq!(beta(app!(mult(), 1.into(), 3.into()), HAP, 0, false),  3.into());
    assert_eq!(beta(app!(mult(), 3.into(), 1.into()), HAP, 0, false),  3.into());
    assert_eq!(beta(app!(mult(), 5.into(), 0.into()), HAP, 0, false),  0.into());
    assert_eq!(beta(app!(mult(), 0.into(), 5.into()), HAP, 0, false),  0.into());
}

#[test]
fn church_exponentiation() {
    assert_eq!(beta(app!(pow(), 2.into(), 4.into()), HAP, 0, false), 16.into());
    assert_eq!(beta(app!(pow(), 1.into(), 3.into()), HAP, 0, false),  1.into());
    assert_eq!(beta(app!(pow(), 3.into(), 1.into()), HAP, 0, false),  3.into());
    assert_eq!(beta(app!(pow(), 5.into(), 0.into()), HAP, 0, false),  1.into());
    assert_eq!(beta(app!(pow(), 0.into(), 5.into()), HAP, 0, false),  0.into());
}

#[test]
fn church_division() {
    assert_eq!(beta(app!(div(), 2.into(), 2.into()), HAP, 0, false), (1.into(), 0.into()).into());
    assert_eq!(beta(app!(div(), 3.into(), 2.into()), HAP, 0, false), (1.into(), 1.into()).into());
    assert_eq!(beta(app!(div(), 5.into(), 2.into()), HAP, 0, false), (2.into(), 1.into()).into());
    assert_eq!(beta(app!(div(), 2.into(), 1.into()), HAP, 0, false), (2.into(), 0.into()).into());
    assert_eq!(beta(app!(div(), 0.into(), 3.into()), HAP, 0, false), (0.into(), 0.into()).into());
}

#[test]
fn church_quotient() {
    assert_eq!(beta(app!(quot(), 2.into(), 2.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(quot(), 3.into(), 2.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(quot(), 5.into(), 2.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(quot(), 2.into(), 1.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(quot(), 0.into(), 3.into()), HAP, 0, false), 0.into());
}

#[test]
fn church_remainder() {
    assert_eq!(beta(app!(rem(), 2.into(), 2.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(rem(), 3.into(), 2.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(rem(), 2.into(), 5.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(rem(), 2.into(), 1.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(rem(), 0.into(), 3.into()), HAP, 0, false), 0.into());
}

#[test]
fn church_factorial() {
    assert_eq!(beta(app!(fac(), 0.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(fac(), 1.into()), HAP, 0, false), 1.into());
    assert_eq!(beta(app!(fac(), 2.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(fac(), 3.into()), HAP, 0, false), 6.into());
}

#[test]
fn church_min() {
    assert_eq!(beta(app!(min(), 0.into(), 0.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(min(), 4.into(), 4.into()), HAP, 0, false), 4.into());
    assert_eq!(beta(app!(min(), 2.into(), 3.into()), HAP, 0, false), 2.into());
    assert_eq!(beta(app!(min(), 5.into(), 3.into()), HAP, 0, false), 3.into());
    assert_eq!(beta(app!(min(), 0.into(), 1.into()), HAP, 0, false), 0.into());
}

#[test]
fn church_max() {
    assert_eq!(beta(app!(max(), 0.into(), 0.into()), HAP, 0, false), 0.into());
    assert_eq!(beta(app!(max(), 4.into(), 4.into()), HAP, 0, false), 4.into());
    assert_eq!(beta(app!(max(), 2.into(), 3.into()), HAP, 0, false), 3.into());
    assert_eq!(beta(app!(max(), 5.into(), 3.into()), HAP, 0, false), 5.into());
    assert_eq!(beta(app!(max(), 0.into(), 1.into()), HAP, 0, false), 1.into());
}

#[test]
fn church_lshift() {
     assert_eq!(beta(app!(lshift(), 0.into(), 2.into()), HAP, 0, false), 0.into());
     assert_eq!(beta(app!(lshift(), 1.into(), 0.into()), HAP, 0, false), 1.into());
     assert_eq!(beta(app!(lshift(), 2.into(), 0.into()), HAP, 0, false), 2.into());
     assert_eq!(beta(app!(lshift(), 2.into(), 2.into()), HAP, 0, false), 8.into());
     assert_eq!(beta(app!(lshift(), 3.into(), 2.into()), HAP, 0, false), 12.into());
     assert_eq!(beta(app!(lshift(), 2.into(), 3.into()), HAP, 0, false), 16.into());
     assert_eq!(beta(app!(lshift(), 5.into(), 1.into()), HAP, 0, false), 10.into());
}

#[test]
fn church_rshift() {
     assert_eq!(beta(app!(rshift(), 1.into(), 0.into()), HAP, 0, false), 1.into());
     assert_eq!(beta(app!(rshift(), 2.into(), 0.into()), HAP, 0, false), 2.into());
     assert_eq!(beta(app!(rshift(), 0.into(), 2.into()), HAP, 0, false), 0.into());
     assert_eq!(beta(app!(rshift(), 2.into(), 1.into()), HAP, 0, false), 1.into());
     assert_eq!(beta(app!(rshift(), 2.into(), 2.into()), HAP, 0, false), 0.into());
     assert_eq!(beta(app!(rshift(), 5.into(), 1.into()), HAP, 0, false), 2.into());
     assert_eq!(beta(app!(rshift(), 9.into(), 1.into()), HAP, 0, false), 4.into());
     assert_eq!(beta(app!(rshift(), 9.into(), 2.into()), HAP, 0, false), 2.into());
     assert_eq!(beta(app!(rshift(), 7.into(), 1.into()), HAP, 0, false), 3.into());
}

#[test]
fn church_is_even() {
     assert_eq!(beta(app!(is_even(), 0.into()), HAP, 0, false), true.into());
     assert_eq!(beta(app!(is_even(), 1.into()), HAP, 0, false), false.into());
     assert_eq!(beta(app!(is_even(), 2.into()), HAP, 0, false), true.into());
     assert_eq!(beta(app!(is_even(), 8.into()), HAP, 0, false), true.into());
     assert_eq!(beta(app!(is_even(), 9.into()), HAP, 0, false), false.into());
}

#[test]
fn church_is_odd() {
     assert_eq!(beta(app!(is_odd(), 0.into()), HAP, 0, false), false.into());
     assert_eq!(beta(app!(is_odd(), 1.into()), HAP, 0, false), true.into());
     assert_eq!(beta(app!(is_odd(), 2.into()), HAP, 0, false), false.into());
     assert_eq!(beta(app!(is_odd(), 8.into()), HAP, 0, false), false.into());
     assert_eq!(beta(app!(is_odd(), 9.into()), HAP, 0, false), true.into());
}
