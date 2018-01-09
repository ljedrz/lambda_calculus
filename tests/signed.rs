#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::num::signed::*;

#[test]
fn signed_neg() {
    assert_eq!(beta(app(neg(), (-2).into_signed()), NOR, 0), beta(2.into_signed(), NOR, 0));
    assert_eq!(beta(app(neg(), (-1).into_signed()), NOR, 0), beta(1.into_signed(), NOR, 0));
    assert_eq!(beta(app(neg(), 0.into_signed()), NOR, 0), beta(0.into_signed(), NOR, 0));
}

#[test]
fn signed_simplify() {
    assert_eq!(beta(app(simplify(), (0, 0).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(), (1, 1).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(), (2, 2).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(), (1, 0).into_church()), NOR, 0), (1, 0).into_church());
    assert_eq!(beta(app(simplify(), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(simplify(), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
    assert_eq!(beta(app(simplify(), (1, 2).into_church()), NOR, 0), (0, 1).into_church());
    assert_eq!(beta(app(simplify(), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(simplify(), (5, 2).into_church()), NOR, 0), (3, 0).into_church());
}

#[test]
fn signed_modulus() {
    assert_eq!(beta(app(modulus(), (-2).into_signed()), NOR, 0), 2.into_church());
    assert_eq!(beta(app(modulus(), (-1).into_signed()), NOR, 0), 1.into_church());
    assert_eq!(beta(app(modulus(), 0.into_signed()), NOR, 0), 0.into_church());
    assert_eq!(beta(app(modulus(), 1.into_signed()), NOR, 0), 1.into_church());
    assert_eq!(beta(app(modulus(), 2.into_signed()), NOR, 0), 2.into_church());
}

#[test]
fn signed_add() {
    assert_eq!(beta(app!(add(), 0.into_signed(), 0.into_signed()), NOR, 0), 0.into_signed());
    assert_eq!(beta(app!(add(), 1.into_signed(), 0.into_signed()), NOR, 0), 1.into_signed());
    assert_eq!(beta(app!(add(), 2.into_signed(), 0.into_signed()), NOR, 0), 2.into_signed());
    assert_eq!(beta(app!(add(), 0.into_signed(), (-1).into_signed()), NOR, 0), (-1).into_signed());
    assert_eq!(beta(app!(add(), 0.into_signed(), (-2).into_signed()), NOR, 0), (-2).into_signed());
    assert_eq!(beta(app!(add(), 4.into_signed(), 5.into_signed()), NOR, 0), 9.into_signed());
    assert_eq!(beta(app!(add(), (-4).into_signed(), 5.into_signed()), NOR, 0), 1.into_signed());
    assert_eq!(beta(app!(add(), 4.into_signed(), (-5).into_signed()), NOR, 0), (-1).into_signed());
    assert_eq!(beta(app!(add(), 4.into_signed(), (-4).into_signed()), NOR, 0), 0.into_signed());
}

#[test]
fn signed_sub() {
    assert_eq!(beta(app!(sub(), 0.into_signed(), 0.into_signed()), NOR, 0), 0.into_signed());
    assert_eq!(beta(app!(sub(), 1.into_signed(), 0.into_signed()), NOR, 0), 1.into_signed());
    assert_eq!(beta(app!(sub(), 2.into_signed(), 0.into_signed()), NOR, 0), 2.into_signed());
    assert_eq!(beta(app!(sub(), 0.into_signed(), (-1).into_signed()), NOR, 0), 1.into_signed());
    assert_eq!(beta(app!(sub(), 0.into_signed(), (-2).into_signed()), NOR, 0), 2.into_signed());
    assert_eq!(beta(app!(sub(), 4.into_signed(), 5.into_signed()), NOR, 0), (-1).into_signed());
    assert_eq!(beta(app!(sub(), 3.into_signed(), 2.into_signed()), NOR, 0), 1.into_signed());
    assert_eq!(beta(app!(sub(), 2.into_signed(), 3.into_signed()), NOR, 0), (-1).into_signed());
    assert_eq!(beta(app!(sub(), (-4).into_signed(), 5.into_signed()), NOR, 0), (-9).into_signed());
    assert_eq!(beta(app!(sub(), 4.into_signed(), (-5).into_signed()), NOR, 0), 9.into_signed());
    assert_eq!(beta(app!(sub(), 4.into_signed(), (-4).into_signed()), NOR, 0), 8.into_signed());
}
