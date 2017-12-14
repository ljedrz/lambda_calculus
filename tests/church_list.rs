#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::church::list::*;
use lambda::church::numerals::{plus, is_zero};
use lambda::church::boolean::fls;

#[test]
fn church_last() {
    let list1 = || { vec![1].into_church() };
    let list2 = || { vec![0, 1, 2, 3, 4].into_church() };

    assert_eq!(beta(app(last(), nil()), HAP, 0), nil());
    assert_eq!(beta(app(last(), list1()), HAP, 0), 1.into_church());
    assert_eq!(beta(app(last(), list2()), HAP, 0), 4.into_church());
}

#[test]
fn church_init() {
    let list1 = || { vec![0, 1, 2, 3, 4].into_church() };
    let list2 = || { vec![0, 1, 2, 3].into_church() };
    let list3 = || { vec![2, 3].into_church() };
    let list4 = || { vec![2].into_church() };

    assert_eq!(beta(app(init(), list1()), HAP, 0), list2());
    assert_eq!(beta(app(init(), list3()), HAP, 0), list4());
    assert_eq!(beta(app(init(), list4()), HAP, 0), nil());
    assert_eq!(beta(app(init(), nil()), HAP, 0), nil());
}

#[test]
fn church_zip() {
    let l1 = || { vec![0].into_church() };
    let l2 = || { vec![0, 1, 2].into_church() };
    let l3 = || { vec![2, 1].into_church() };
    let p1 = || { vec![(0, 0)].into_church() };
    let p2 = || { vec![(0, 0), (1, 1), (2, 2)].into_church() };
    let p3 = || { vec![(0, 2), (1, 1)].into_church() };

    assert_eq!(beta(app!(zip(), nil(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(zip(), nil(), l1()), HAP, 0), nil());
    assert_eq!(beta(app!(zip(), l1(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(zip(), l1(), l1()), HAP, 0), p1());
    assert_eq!(beta(app!(zip(), l1(), l2()), HAP, 0), p1());
    assert_eq!(beta(app!(zip(), l2(), l1()), HAP, 0), p1());
    assert_eq!(beta(app!(zip(), l2(), l2()), HAP, 0), p2());
    assert_eq!(beta(app!(zip(), l2(), l3()), HAP, 0), p3());
}

#[test]
fn church_zip_with() {
    let l1 = || { vec![1].into_church() };
    let l2 = || { vec![2].into_church() };
    let l3 = || { vec![1, 2, 3].into_church() };
    let l4 = || { vec![2, 4, 6].into_church() };
    let l5 = || { vec![3].into_church() };

    assert_eq!(beta(app!(zip_with(), plus(), nil(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(zip_with(), plus(), nil(), l1()), HAP, 0), nil());
    assert_eq!(beta(app!(zip_with(), abs!(2, Var(1)), l1(), l1()), HAP, 0), l1());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l1()), HAP, 0), l2());
    assert_eq!(beta(app!(zip_with(), plus(), l3(), l3()), HAP, 0), l4());
    assert_eq!(beta(app!(zip_with(), plus(), l4(), l1()), HAP, 0), l5());
    assert_eq!(beta(app!(zip_with(), plus(), l1(), l4()), HAP, 0), l5());
    assert_eq!(beta(app!(zip_with(), fls(), l1(), l4()), HAP, 0), l2());
    assert_eq!(beta(app!(zip_with(), fls(), l4(), l1()), HAP, 0), l1());
}

#[test]
fn church_take() {
    let l1 = || { vec![0].into_church() };
    let l2 = || { vec![0, 1].into_church() };
    let l3 = || { vec![0, 1, 2].into_church() };
    let l4 = || { vec![0, 1, 2, 3].into_church() };

    assert_eq!(beta(app!(take(), 5.into_church(), l4()), HAP, 0), l4());
    assert_eq!(beta(app!(take(), 4.into_church(), l4()), HAP, 0), l4());
    assert_eq!(beta(app!(take(), 3.into_church(), l4()), HAP, 0), l3());
    assert_eq!(beta(app!(take(), 2.into_church(), l4()), HAP, 0), l2());
    assert_eq!(beta(app!(take(), 1.into_church(), l4()), HAP, 0), l1());
    assert_eq!(beta(app!(take(), 0.into_church(), l4()), HAP, 0), nil());
    assert_eq!(beta(app!(take(), 1.into_church(), l1()), HAP, 0), l1());
    assert_eq!(beta(app!(take(), 0.into_church(), l1()), HAP, 0), nil());
    assert_eq!(beta(app!(take(), 1.into_church(), nil()), HAP, 0), nil());
}

#[test]
fn church_take_while() {
    let l1 = || { vec![0, 0, 2, 3].into_church() };
    let l2 = || { vec![0, 0].into_church() };
    let l3 = || { vec![1, 4, 2, 3].into_church() };
    let l4 = || { vec![0, 4, 0, 0].into_church() };
    let l5 = || { vec![0].into_church() };

    assert_eq!(beta(app!(take_while(), is_zero(), nil()), HAP, 0), nil());
    assert_eq!(beta(app!(take_while(), is_zero(), l1()), HAP, 0), l2());
    assert_eq!(beta(app!(take_while(), is_zero(), l2()), HAP, 0), l2());
    assert_eq!(beta(app!(take_while(), is_zero(), l3()), HAP, 0), nil());
    assert_eq!(beta(app!(take_while(), is_zero(), l4()), HAP, 0), l5());
}
