//! [Stump-Fu numerals](http://homepage.cs.uiowa.edu/~astump/papers/stump-fu-jfp-2016.pdf)

use term::{Term, abs, app};
use term::Term::*;
use data::numerals::church as church;
use data::numerals::convert::IntoChurchNum;
use data::boolean::{tru, fls};

/// Produces a Stump-Fu-encoded number zero.
///
/// ZERO := λf.λa.a = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_stumpfu());
/// ```
pub fn zero() -> Term { abs!(2, Var(1)) }

/// Applied to a Stump-Fu-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO := λn.n (λx.FALSE) TRUE =  λ 1 (λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::is_zero;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_zero(), 0.into_stumpfu()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_zero(), 1.into_stumpfu()), NOR, 0), false.into());
/// ```
pub fn is_zero() -> Term {
    abs(app!(Var(1), abs!(2, fls()), tru()))
}

/// Produces a Stump-Fu-encoded number one.
///
/// ONE := λf.λa.f CHURCH_ONE ZERO = λ λ 2 CHURCH_ONE ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_stumpfu());
/// ```
pub fn one() -> Term { abs!(2, app!(Var(2), 1.into_church(), zero())) }

/// Applied to a Stump-Fu-encoded number it produces its successor.
///
/// SUCC := λn.n (λcpfa.f (CHURCH_SUCC c) n) ONE = λ 1 (λ λ λ λ 2 (CHURCH_SUCC 4) 5) ONE
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_stumpfu()), NOR, 0), 1.into_stumpfu());
/// assert_eq!(beta(app(succ(), 1.into_stumpfu()), NOR, 0), 2.into_stumpfu());
/// ```
pub fn succ() -> Term {
    abs(app!(
        Var(1),
        abs!(4, app!(Var(2), app(church::succ(), Var(4)), Var(5))),
        one()
    ))
}

/// Applied to a Stump-Fu-encoded number it produces its predecessor.
///
/// PRED := λn.n (λcs.s) ZERO = λ 1 (λ λ 1) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into_stumpfu()), NOR, 0), 0.into_stumpfu());
/// assert_eq!(beta(app(pred(), 3.into_stumpfu()), NOR, 0), 2.into_stumpfu());
/// ```
pub fn pred() -> Term {
    abs(app!(Var(1), abs!(2, Var(1)), zero()))
}

/// Applied to two Stump-Fu-encoded numbers it produces their sum.
///
/// ADD := λnm.n (λcp.c SUCC m) m = λ λ 2 (λ λ 2 SUCC 3) 1
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::stumpfu::add;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(add(), 1.into_stumpfu(), 2.into_stumpfu()), NOR, 0), 3.into_stumpfu());
/// assert_eq!(beta(app!(add(), 2.into_stumpfu(), 3.into_stumpfu()), NOR, 0), 5.into_stumpfu());
/// ```
pub fn add() -> Term {
    abs!(2, app!(
        Var(2),
        abs!(2, app!(Var(2), succ(), Var(3))),
        Var(1)
    ))
}
