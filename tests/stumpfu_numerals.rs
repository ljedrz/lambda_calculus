#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::stumpfu::numerals::*;

#[test]
fn stumpfu_succ() {
    assert_eq!(beta(app!(succ(), 0.into_stumpfu()), HAP, 0), 1.into_stumpfu());
    assert_eq!(beta(app!(succ(), 1.into_stumpfu()), HAP, 0), 2.into_stumpfu());
    assert_eq!(beta(app!(succ(), 2.into_stumpfu()), HAP, 0), 3.into_stumpfu());
}

#[test]
fn stumpfu_pred() {
    assert_eq!(beta(app!(pred(), 0.into_stumpfu()), HAP, 0), 0.into_stumpfu());
    assert_eq!(beta(app!(pred(), 1.into_stumpfu()), HAP, 0), 0.into_stumpfu());
    assert_eq!(beta(app!(pred(), 5.into_stumpfu()), HAP, 0), 4.into_stumpfu());
}

#[test]
fn stumpfu_add() {
    assert_eq!(beta(app!(add(), 0.into_stumpfu(), 0.into_stumpfu()), HAP, 0), 0.into_stumpfu());
    assert_eq!(beta(app!(add(), 0.into_stumpfu(), 1.into_stumpfu()), HAP, 0), 1.into_stumpfu());
    assert_eq!(beta(app!(add(), 1.into_stumpfu(), 0.into_stumpfu()), HAP, 0), 1.into_stumpfu());
    assert_eq!(beta(app!(add(), 2.into_stumpfu(), 3.into_stumpfu()), HAP, 0), 5.into_stumpfu());
}
