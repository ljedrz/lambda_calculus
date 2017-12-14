#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::scott::numerals::*;

#[test]
fn scott_succ() {
    assert_eq!(beta(app!(succ(), 0.into_scott()), HAP, 0), 1.into_scott());
    assert_eq!(beta(app!(succ(), 1.into_scott()), HAP, 0), 2.into_scott());
    assert_eq!(beta(app!(succ(), 2.into_scott()), HAP, 0), 3.into_scott());
}

#[test]
fn scott_pred() {
    assert_eq!(beta(app!(pred(), 0.into_scott()), HAP, 0), 0.into_scott());
    assert_eq!(beta(app!(pred(), 1.into_scott()), HAP, 0), 0.into_scott());
    assert_eq!(beta(app!(pred(), 5.into_scott()), HAP, 0), 4.into_scott());
}
