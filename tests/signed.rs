#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::num::signed::*;

#[test]
fn signed_neg() {
    assert_eq!(beta(app(neg(), (-2).into_signed(Church)), NOR, 0), beta(2.into_signed(Church), NOR, 0));
    assert_eq!(beta(app(neg(), (-1).into_signed(Scott)), NOR, 0), beta(1.into_signed(Scott), NOR, 0));
    assert_eq!(beta(app(neg(), 0.into_signed(Parigot)), NOR, 0), beta(0.into_signed(Parigot), NOR, 0));
}

#[test]
fn signed_simplify() {
    assert_eq!(beta(app(simplify(Church), (0, 0).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (1, 1).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (2, 2).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (1, 0).into_church()), NOR, 0), (1, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
    assert_eq!(beta(app(simplify(Church), (1, 2).into_church()), NOR, 0), (0, 1).into_church());
    assert_eq!(beta(app(simplify(Church), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(simplify(Church), (5, 2).into_church()), NOR, 0), (3, 0).into_church());
}

#[test]
fn signed_modulus() {
    assert_eq!(beta(app(modulus(Church), (-2).into_signed(Church)), NOR, 0),  2.into_church());
    assert_eq!(beta(app(modulus(Church), (-1).into_signed(Church)), NOR, 0),  1.into_church());
    assert_eq!(beta(app(modulus(StumpFu),  0.into_signed(StumpFu)), NOR, 0), 0.into_stumpfu());
    assert_eq!(beta(app(modulus(Parigot),  2.into_signed(Parigot)), NOR, 0), 2.into_parigot());
}

#[test]
fn signed_add() {
    assert_eq!(beta(app!(add(Church), 0.into_signed(Church), 0.into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(add(Church), 1.into_signed(Church), 0.into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(add(Church), 2.into_signed(Church), 0.into_signed(Church)), NOR, 0), 2.into_signed(Church));
    assert_eq!(beta(app!(add(Church), 0.into_signed(Church), (-1).into_signed(Church)), NOR, 0), (-1).into_signed(Church));
    assert_eq!(beta(app!(add(Church), 0.into_signed(Church), (-2).into_signed(Church)), NOR, 0), (-2).into_signed(Church));
    assert_eq!(beta(app!(add(Church), 4.into_signed(Church), 5.into_signed(Church)), NOR, 0), 9.into_signed(Church));
    assert_eq!(beta(app!(add(Church), (-4).into_signed(Church), 5.into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(add(Church), 4.into_signed(Church), (-5).into_signed(Church)), NOR, 0), (-1).into_signed(Church));
    assert_eq!(beta(app!(add(Church), 4.into_signed(Church), (-4).into_signed(Church)), NOR, 0), 0.into_signed(Church));
}

#[test]
fn signed_sub() {
    assert_eq!(beta(app!(sub(Church), 0.into_signed(Church), 0.into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 1.into_signed(Church), 0.into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 2.into_signed(Church), 0.into_signed(Church)), NOR, 0), 2.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 0.into_signed(Church), (-1).into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 0.into_signed(Church), (-2).into_signed(Church)), NOR, 0), 2.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 4.into_signed(Church), 5.into_signed(Church)), NOR, 0), (-1).into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 3.into_signed(Church), 2.into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 2.into_signed(Church), 3.into_signed(Church)), NOR, 0), (-1).into_signed(Church));
    assert_eq!(beta(app!(sub(Church), (-4).into_signed(Church), 5.into_signed(Church)), NOR, 0), (-9).into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 4.into_signed(Church), (-5).into_signed(Church)), NOR, 0), 9.into_signed(Church));
    assert_eq!(beta(app!(sub(Church), 4.into_signed(Church), (-4).into_signed(Church)), NOR, 0), 8.into_signed(Church));
}

#[test]
fn signed_mul() {
    assert_eq!(beta(app!(mul(Church), 0.into_signed(Church), 0.into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 1.into_signed(Church), 0.into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 2.into_signed(Church), 0.into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 0.into_signed(Church), (-1).into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 0.into_signed(Church), (-2).into_signed(Church)), NOR, 0), 0.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 1.into_signed(Church), 1.into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 1.into_signed(Church), (-1).into_signed(Church)), NOR, 0), (-1).into_signed(Church));
    assert_eq!(beta(app!(mul(Church), (-1).into_signed(Church), (-1).into_signed(Church)), NOR, 0), 1.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), (-2).into_signed(Church), (-1).into_signed(Church)), NOR, 0), 2.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 2.into_signed(Church), 2.into_signed(Church)), NOR, 0), 4.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), 2.into_signed(Church), 3.into_signed(Church)), NOR, 0), 6.into_signed(Church));
    assert_eq!(beta(app!(mul(Church), (-2).into_signed(Church), 3.into_signed(Church)), NOR, 0), (-6).into_signed(Church));
}
