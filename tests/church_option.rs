#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::option::*;
use lambda::church::numerals::succ;

#[test]
fn church_none() {
    assert_eq!(beta(none(), HAP, 0), none());
}

#[test]
fn church_some() {
    assert_eq!(beta(app(some(), 3.into_church()), HAP, 0), Some(3.into_church()).into_church());
}

#[test]
fn church_is_some() {
    assert_eq!(beta(app(is_some(), none()), HAP, 0), false.into_church());
    assert_eq!(beta(app(is_some(), Some(3.into_church()).into_church()), HAP, 0), true.into_church());
}

#[test]
fn church_is_none() {
    assert_eq!(beta(app(is_none(), none()), HAP, 0), true.into_church());
    assert_eq!(beta(app(is_none(), Some(3).into_church()), HAP, 0), false.into_church());
}

#[test]
fn church_map_or() {
    assert_eq!(beta(app!(map_or(), 5.into_church(), succ(), none()), HAP, 0), 5.into_church());
    assert_eq!(beta(app!(map_or(), 5.into_church(), succ(), Some(1).into_church()), HAP, 0), 2.into_church());
}

#[test]
fn church_unwrap_or() {
    assert_eq!(beta(app!(unwrap_or(), 5.into_church(), none()), HAP, 0), 5.into_church());
    assert_eq!(beta(app!(unwrap_or(), 5.into_church(), Some(1).into_church()), HAP, 0), 1.into_church());
}
