#![cfg(feature = "church")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::option::*;
use lambda::church::numerals::succ;

#[test]
fn church_none() {
    assert_eq!(beta(None.into(), HAP, 0), none());
}

#[test]
fn church_some() {
    assert_eq!(beta(app(some(), 3.into()), HAP, 0), Some(3.into()).into());
}

#[test]
fn church_is_some() {
    assert_eq!(beta(app(is_some(), None.into()), HAP, 0), false.into());
    assert_eq!(beta(app(is_some(), Some(3.into()).into()), HAP, 0), true.into());
}

#[test]
fn church_is_none() {
    assert_eq!(beta(app(is_none(), None.into()), HAP, 0), true.into());
    assert_eq!(beta(app(is_none(), Some(3.into()).into()), HAP, 0), false.into());
}

#[test]
fn church_map_or() {
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), None.into()), HAP, 0), 5.into());
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), Some(1.into()).into()), HAP, 0), 2.into());
}

#[test]
fn church_unwrap_or() {
    assert_eq!(beta(app!(unwrap_or(), 5.into(), None.into()), HAP, 0), 5.into());
    assert_eq!(beta(app!(unwrap_or(), 5.into(), Some(1.into()).into()), HAP, 0), 1.into());
}
