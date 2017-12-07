#![cfg(not(feature = "no_church"))]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::lists::*;

#[test]
fn test_last() {
    let list1 = || { Term::from(vec![1.into()]) };
    let list2 = || { Term::from(vec![0.into(), 1.into(), 2.into(), 3.into(), 4.into()]) };

    assert_eq!(beta(app(last(), nil()), NOR, 0, false), nil());
    assert_eq!(beta(app(last(), list1()), NOR, 0, false), 1.into());
    assert_eq!(beta(app(last(), list2()), NOR, 0, false), 4.into());

    assert_eq!(beta(app(last(), nil()), HNO, 0, false), nil());
    assert_eq!(beta(app(last(), list1()), HNO, 0, false), 1.into());
    assert_eq!(beta(app(last(), list2()), HNO, 0, false), 4.into());

    assert_eq!(beta(app(last(), nil()), HAP, 0, false), nil());
    assert_eq!(beta(app(last(), list1()), HAP, 0, false), 1.into());
    assert_eq!(beta(app(last(), list2()), HAP, 0, false), 4.into());
}
