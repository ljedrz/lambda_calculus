#![cfg(not(feature = "no_church"))]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::term::Term;
use lambda::church::lists::*;
use lambda::reduction::beta;
use lambda::reduction::Order::*;
use lambda::church::numerals::{is_zero, plus, succ};

#[test]
fn list_from_vector() {
    let list_from_vec = Term::from(vec![1.into(), 1.into(), 0.into()]);
    let list_pushed = nil()
        .push(0.into())
        .and_then(|t| t.push(1.into()))
        .and_then(|t| t.push(1.into()))
        .unwrap();

    assert_eq!(list_from_vec, list_pushed);
}

#[test]
fn list_length() {
    let list0 = nil();
    assert_eq!(list0.len(), Ok(0));
    let list1 = list0.push(1.into()).unwrap();
    assert_eq!(list1.len(), Ok(1));
    let list2 = list1.push(1.into()).unwrap();
    assert_eq!(list2.len(), Ok(2));
    let list3 = list2.push(1.into()).unwrap();
    assert_eq!(list3.len(), Ok(3));
}

#[test]
fn list_operations() {
    let list_354 = Term::from(vec![3.into(), 5.into(), 4.into()]);

    assert!(list_354.is_list());

    assert_eq!(list_354.head_ref(), Ok(&3.into()));
    assert_eq!(list_354.tail_ref(), Ok(&Term::from(vec![5.into(), 4.into()])));

    assert_eq!(list_354.tail_ref().and_then(|t| t.head_ref()), Ok(&5.into()));
    assert_eq!(list_354.tail_ref()
               .and_then(|t| t.tail_ref())
               .and_then(|t| t.head_ref()), Ok(&4.into()));

    let unconsed = list_354.uncons();
    assert_eq!(unconsed, Ok((3.into(), Term::from(vec![5.into(), 4.into()]))));
}

#[test]
fn iterating_list() {
    let list010 = Term::from(vec![0.into(), 1.into(), 0.into()]);
    let mut iter = list010.into_iter();

    assert_eq!(iter.next(), Some(0.into()));
    assert_eq!(iter.next(), Some(1.into()));
    assert_eq!(iter.next(), Some(0.into()));
    assert_eq!(iter.next(), None);
}

#[test]
fn indexing_list() {
    let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into(), 4.into()]);

    assert_eq!(list[0], 0.into());
    assert_eq!(list[1], 1.into());
    assert_eq!(list[2], 2.into());
    assert_eq!(list[3], 3.into());
    assert_eq!(list[4], 4.into());
}

#[test]
fn cbv_list_functions() {
    let l = Term::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);

    assert_eq!(beta(app!( length(), l.clone()), HAP, 0, false), 4.into());

    assert_eq!(beta(app!(reverse(), l.clone()), HAP, 0, false),
        Term::from(vec![4.into(), 3.into(), 2.into(), 1.into()]));

    assert_eq!(beta(app!(list(), 4.into(), 1.into(), 2.into(), 3.into(), 4.into()), HAP, 0, false), l);

    assert_eq!(beta(app!(append(), Term::from(vec![1.into(), 2.into()]),
        Term::from(vec![3.into(), 4.into()])), HAP, 0, false), l);

    assert_eq!(beta(app!(map(), succ(), l.clone()), HAP, 0, false),
        Term::from(vec![2.into(), 3.into(), 4.into(), 5.into()]));

    assert_eq!(beta(app!(foldl(), plus(), 0.into(), l.clone()), HAP, 0, false), 10.into());
    assert_eq!(beta(app!(foldr(), plus(), 0.into(), l.clone()), HAP, 0, false), 10.into());

    assert_eq!(beta(app!(filter(), is_zero(), l.clone()), HAP, 0, false), Term::from(vec![]));
}
