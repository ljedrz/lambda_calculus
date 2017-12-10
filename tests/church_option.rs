#![cfg(not(feature = "no_church"))]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::option::*;
use lambda::church::numerals::succ;

#[test]
fn test_none() {
    assert_eq!(beta(None.into(), NOR, 0, false), none());
    assert_eq!(beta(None.into(), HNO, 0, false), none());
    assert_eq!(beta(None.into(), HAP, 0, false), none());
}

#[test]
fn test_some() {
    assert_eq!(
        beta(Some(3.into()).into(), NOR, 0, false),
        beta(app(some(), 3.into()), NOR, 0, false)
    );
    assert_eq!(
        beta(Some(3.into()).into(), HNO, 0, false),
        beta(app(some(), 3.into()), HNO, 0, false)
    );
    assert_eq!(
        beta(Some(3.into()).into(), HAP, 0, false),
        beta(app(some(), 3.into()), HAP, 0, false)
    );
}

#[test]
fn test_is_some() {
    assert_eq!(beta(app(is_some(), None.into()), NOR, 0, false), false.into());
    assert_eq!(beta(app(is_some(), Some(3.into()).into()), NOR, 0, false), true.into());

    assert_eq!(beta(app(is_some(), None.into()), HNO, 0, false), false.into());
    assert_eq!(beta(app(is_some(), Some(3.into()).into()), HNO, 0, false), true.into());

    assert_eq!(beta(app(is_some(), None.into()), HAP, 0, false), false.into());
    assert_eq!(beta(app(is_some(), Some(3.into()).into()), HAP, 0, false), true.into());
}

#[test]
fn test_is_none() {
    assert_eq!(beta(app(is_none(), None.into()), NOR, 0, false), true.into());
    assert_eq!(beta(app(is_none(), Some(3.into()).into()), NOR, 0, false), false.into());

    assert_eq!(beta(app(is_none(), None.into()), HNO, 0, false), true.into());
    assert_eq!(beta(app(is_none(), Some(3.into()).into()), HNO, 0, false), false.into());

    assert_eq!(beta(app(is_none(), None.into()), HAP, 0, false), true.into());
    assert_eq!(beta(app(is_none(), Some(3.into()).into()), HAP, 0, false), false.into());
}

#[test]
fn test_map_or() {
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), None.into()), NOR, 0, false), 5.into());
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), Some(1.into()).into()), NOR, 0, false), 2.into());

    assert_eq!(beta(app!(map_or(), 5.into(), succ(), None.into()), HNO, 0, false), 5.into());
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), Some(1.into()).into()), HNO, 0, false), 2.into());

    assert_eq!(beta(app!(map_or(), 5.into(), succ(), None.into()), HAP, 0, false), 5.into());
    assert_eq!(beta(app!(map_or(), 5.into(), succ(), Some(1.into()).into()), HAP, 0, false), 2.into());
}
