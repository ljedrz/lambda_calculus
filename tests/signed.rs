#![cfg(feature = "encoding")]

#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::data::signed::church::*;

fn convert(i: i32) -> Term {
    let base_term = app(to_signed(), (i.abs() as usize).into_church());
    if i >= 0 { base_term } else { app(negate(), base_term) }
}

fn beta_convert(i: i32) -> Term {
    beta(convert(i), NOR, 0)
}

#[test]
fn church_negate() {
    assert_eq!(beta(app(negate(), convert(-2)), NOR, 0), beta(convert(2), NOR, 0));
    assert_eq!(beta(app(negate(), convert(-1)), NOR, 0), beta(convert(1), NOR, 0));
    assert_eq!(beta(app(negate(), convert(0)), NOR, 0), beta(convert(0), NOR, 0));
}

#[test]
fn church_normalize() {
    assert_eq!(beta(app(normalize(), (0, 0).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(normalize(), (1, 1).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(normalize(), (2, 2).into_church()), NOR, 0), (0, 0).into_church());
    assert_eq!(beta(app(normalize(), (1, 0).into_church()), NOR, 0), (1, 0).into_church());
    assert_eq!(beta(app(normalize(), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(normalize(), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
    assert_eq!(beta(app(normalize(), (1, 2).into_church()), NOR, 0), (0, 1).into_church());
    assert_eq!(beta(app(normalize(), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
    assert_eq!(beta(app(normalize(), (5, 2).into_church()), NOR, 0), (3, 0).into_church());
}

#[test]
fn church_absolute_value() {
    assert_eq!(beta(app(absolute_value(), convert(-2)), NOR, 0), 2.into_church());
    assert_eq!(beta(app(absolute_value(), convert(-1)), NOR, 0), 1.into_church());
    assert_eq!(beta(app(absolute_value(), convert(0)), NOR, 0), 0.into_church());
    assert_eq!(beta(app(absolute_value(), convert(1)), NOR, 0), 1.into_church());
    assert_eq!(beta(app(absolute_value(), convert(2)), NOR, 0), 2.into_church());
}

#[test]
fn church_signed_add() {
    assert_eq!(beta(app!(signed_add(), convert(0), convert(0)), NOR, 0), beta_convert(0));
    assert_eq!(beta(app!(signed_add(), convert(1), convert(0)), NOR, 0), beta_convert(1));
    assert_eq!(beta(app!(signed_add(), convert(2), convert(0)), NOR, 0), beta_convert(2));
    assert_eq!(beta(app!(signed_add(), convert(0), convert(-1)), NOR, 0), beta_convert(-1));
    assert_eq!(beta(app!(signed_add(), convert(0), convert(-2)), NOR, 0), beta_convert(-2));
    assert_eq!(beta(app!(signed_add(), convert(4), convert(5)), NOR, 0), beta_convert(9));
    assert_eq!(beta(app!(signed_add(), convert(-4), convert(5)), NOR, 0), beta_convert(1));
    assert_eq!(beta(app!(signed_add(), convert(4), convert(-5)), NOR, 0), beta_convert(-1));
    assert_eq!(beta(app!(signed_add(), convert(4), convert(-4)), NOR, 0), beta_convert(0));
}

#[test]
fn church_signed_sub() {
    assert_eq!(beta(app!(signed_sub(), convert(0), convert(0)), NOR, 0), beta_convert(0));
    assert_eq!(beta(app!(signed_sub(), convert(1), convert(0)), NOR, 0), beta_convert(1));
    assert_eq!(beta(app!(signed_sub(), convert(2), convert(0)), NOR, 0), beta_convert(2));
    assert_eq!(beta(app!(signed_sub(), convert(0), convert(-1)), NOR, 0), beta_convert(1));
    assert_eq!(beta(app!(signed_sub(), convert(0), convert(-2)), NOR, 0), beta_convert(2));
    assert_eq!(beta(app!(signed_sub(), convert(4), convert(5)), NOR, 0), beta_convert(-1));
    assert_eq!(beta(app!(signed_sub(), convert(3), convert(2)), NOR, 0), beta_convert(1));
    assert_eq!(beta(app!(signed_sub(), convert(2), convert(3)), NOR, 0), beta_convert(-1));
    assert_eq!(beta(app!(signed_sub(), convert(-4), convert(5)), NOR, 0), beta_convert(-9));
    assert_eq!(beta(app!(signed_sub(), convert(4), convert(-5)), NOR, 0), beta_convert(9));
    assert_eq!(beta(app!(signed_sub(), convert(4), convert(-4)), NOR, 0), beta_convert(8));
}
