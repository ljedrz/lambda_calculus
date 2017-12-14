#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::parigot::numerals::*;

#[test]
fn parigot_succ() {
    assert_eq!(beta(app!(succ(), 0.into_parigot()), HAP, 0), 1.into_parigot());
    assert_eq!(beta(app!(succ(), 1.into_parigot()), HAP, 0), 2.into_parigot());
    assert_eq!(beta(app!(succ(), 2.into_parigot()), HAP, 0), 3.into_parigot());
}

#[test]
fn parigot_pred() {
    assert_eq!(beta(app!(pred(), 0.into_parigot()), HAP, 0), 0.into_parigot());
    assert_eq!(beta(app!(pred(), 1.into_parigot()), HAP, 0), 0.into_parigot());
    assert_eq!(beta(app!(pred(), 5.into_parigot()), HAP, 0), 4.into_parigot());
}

#[test]
fn parigot_mult() {
    assert_eq!(beta(app!(mult(), 3.into_parigot(), 4.into_parigot()), HAP, 0), 12.into_parigot());
    assert_eq!(beta(app!(mult(), 1.into_parigot(), 3.into_parigot()), HAP, 0),  3.into_parigot());
    assert_eq!(beta(app!(mult(), 3.into_parigot(), 1.into_parigot()), HAP, 0),  3.into_parigot());
    assert_eq!(beta(app!(mult(), 5.into_parigot(), 0.into_parigot()), HAP, 0),  0.into_parigot());
    assert_eq!(beta(app!(mult(), 0.into_parigot(), 5.into_parigot()), HAP, 0),  0.into_parigot());
}
