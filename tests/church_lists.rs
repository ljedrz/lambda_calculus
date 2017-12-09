#![cfg(not(feature = "no_church"))]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::lists::*;
use lambda::church::numerals::plus;

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

#[test]
fn test_init() {
    let list1 = || { Term::from(vec![0.into(), 1.into(), 2.into(), 3.into(), 4.into()]) };
    let list2 = || { Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]) };
    let list3 = || { Term::from(vec![2.into(), 3.into()]) };
    let list4 = || { Term::from(vec![2.into()]) };

    assert_eq!(beta(app(init(), list1()), NOR, 0, false), list2());
    assert_eq!(beta(app(init(), list3()), NOR, 0, false), list4());
    assert_eq!(beta(app(init(), list4()), NOR, 0, false), nil());
    assert_eq!(beta(app(init(), nil()), NOR, 0, false), nil());

    assert_eq!(beta(app(init(), list1()), HNO, 0, false), list2());
    assert_eq!(beta(app(init(), list3()), HNO, 0, false), list4());
    assert_eq!(beta(app(init(), list4()), HNO, 0, false), nil());
    assert_eq!(beta(app(init(), nil()), HNO, 0, false), nil());

    assert_eq!(beta(app(init(), list1()), HAP, 0, false), list2());
    assert_eq!(beta(app(init(), list3()), HAP, 0, false), list4());
    assert_eq!(beta(app(init(), list4()), HAP, 0, false), nil());
    assert_eq!(beta(app(init(), nil()), HAP, 0, false), nil());
}

#[test]
fn test_zip() {
    let l1 = || { Term::from(vec![0.into()]) };
    let l2 = || { Term::from(vec![0.into(), 1.into(), 2.into()]) };
    let l3 = || { Term::from(vec![2.into(), 1.into()]) };

    let p1 = || { Term::from(vec![(0.into(), 0.into()).into()]) }; // zip(l1, l1)
    let p2 = || { Term::from(vec![
        (0.into(), 0.into()).into(),
        (1.into(), 1.into()).into(),
        (2.into(), 2.into()).into(),
    ])}; //zip(l2, l2)
    let p3 = || { Term::from(vec![
        (0.into(), 2.into()).into(),
        (1.into(), 1.into()).into(),
    ])}; // zip(l2, l3)

    assert_eq!(beta(app!(zip(), nil(), nil()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip(), nil(), l1()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), nil()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), l1()), NOR, 0, false), p1());
    assert_eq!(beta(app!(zip(), l1(), l2()), NOR, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l1()), NOR, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l2()), NOR, 0, false), p2());
    assert_eq!(beta(app!(zip(), l2(), l3()), NOR, 0, false), p3());

    assert_eq!(beta(app!(zip(), nil(), nil()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip(), nil(), l1()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), nil()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), l1()), HNO, 0, false), p1());
    assert_eq!(beta(app!(zip(), l1(), l2()), HNO, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l1()), HNO, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l2()), HNO, 0, false), p2());
    assert_eq!(beta(app!(zip(), l2(), l3()), HNO, 0, false), p3());

    assert_eq!(beta(app!(zip(), nil(), nil()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip(), nil(), l1()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), nil()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip(), l1(), l1()), HAP, 0, false), p1());
    assert_eq!(beta(app!(zip(), l1(), l2()), HAP, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l1()), HAP, 0, false), p1());
    assert_eq!(beta(app!(zip(), l2(), l2()), HAP, 0, false), p2());
    assert_eq!(beta(app!(zip(), l2(), l3()), HAP, 0, false), p3());
}

#[test]
fn test_zip_with() {
    let l1 = || { Term::from(vec![1.into()]) };
    let l2 = || { Term::from(vec![2.into()]) };
    let l3 = || { Term::from(vec![1.into(), 2.into(), 3.into()]) };
    let l4 = || { Term::from(vec![2.into(), 4.into(), 6.into()]) };
    let l5 = || { Term::from(vec![3.into()]) };

    assert_eq!(beta(app!(zip_with(), plus(), nil(), nil()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), nil()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), nil(), l1()), NOR, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l1()), NOR, 0, false), l1());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l1()), NOR, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), plus(), l3(), l3()), NOR, 0, false), l4());
    assert_eq!(beta(app!(zip_with(), plus(), l4(), l1()), NOR, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l4()), NOR, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l4()), NOR, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l4(), l1()), NOR, 0, false), l1());

    assert_eq!(beta(app!(zip_with(), plus(), nil(), nil()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), nil()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), nil(), l1()), HNO, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l1()), HNO, 0, false), l1());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l1()), HNO, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), plus(), l3(), l3()), HNO, 0, false), l4());
    assert_eq!(beta(app!(zip_with(), plus(), l4(), l1()), HNO, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l4()), HNO, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l4()), HNO, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l4(), l1()), HNO, 0, false), l1());

    assert_eq!(beta(app!(zip_with(), plus(), nil(), nil()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), nil()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), plus(), nil(), l1()), HAP, 0, false), nil());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l1()), HAP, 0, false), l1());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l1()), HAP, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), plus(), l3(), l3()), HAP, 0, false), l4());
    assert_eq!(beta(app!(zip_with(), plus(), l4(), l1()), HAP, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l4()), HAP, 0, false), l5());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l4()), HAP, 0, false), l2());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l4(), l1()), HAP, 0, false), l1());
}
