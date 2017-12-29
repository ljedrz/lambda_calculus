#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::option::*;
use lambda::data::num::church::succ;

#[test]
fn option_none() {
    assert_eq!(beta(none(), HAP, 0), none());
}

#[test]
fn option_some() {
    assert_eq!(beta(app(some(), 3.into_church()), HAP, 0), Some(3).into_church());
}

#[test]
fn option_is_some() {
    assert_eq!(beta(app(is_some(), none()), HAP, 0), false.into());
    assert_eq!(beta(app(is_some(), Some(3).into_church()), HAP, 0), true.into());
}

#[test]
fn option_is_none() {
    assert_eq!(beta(app(is_none(), none()), HAP, 0), true.into());
    assert_eq!(beta(app(is_none(), Some(3).into_church()), HAP, 0), false.into());
}

#[test]
fn option_map() {
    assert_eq!(beta(app!(map(), succ(), none()), HAP, 0), none());
    assert_eq!(beta(app!(map(), succ(), Some(1).into_church()), HAP, 0), Some(2).into_church());
}

#[test]
fn option_map_or() {
    assert_eq!(beta(app!(map_or(), 5.into_church(), succ(), none()), HAP, 0), 5.into_church());
    assert_eq!(beta(app!(map_or(), 5.into_church(), succ(), Some(1).into_church()), HAP, 0), 2.into_church());
}

#[test]
fn option_unwrap_or() {
    assert_eq!(beta(app!(unwrap_or(), 5.into_church(), none()), HAP, 0), 5.into_church());
    assert_eq!(beta(app!(unwrap_or(), 5.into_church(), Some(1).into_church()), HAP, 0), 1.into_church());
}

#[test]
fn option_and_then() {
    let some_succ: Term = abs(app(some(), app(succ(), Var(1))));
    let return_none: Term = abs(none());

    assert_eq!(beta(app!(and_then(), none(), some_succ.clone()), NOR, 0), none());
    assert_eq!(beta(app!(and_then(), Some(1).into_church(), return_none.clone()), NOR, 0), none());
    assert_eq!(beta(
        app!(and_then(), Some(1).into_church(), some_succ.clone()), NOR, 0),
        Some(2).into_church()
    );
}
