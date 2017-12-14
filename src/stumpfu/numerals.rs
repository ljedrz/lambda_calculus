//! [Stump-Fu numerals](http://homepage.cs.uiowa.edu/~astump/papers/stump-fu-jfp-2016.pdf)

use term::{Term, abs, app};
use term::Term::*;
use stumpfu::convert::IntoStumpFu;
use church::convert::IntoChurch;
use church::numerals as church;

/// Produces a Stump-Fu-encoded number zero.
///
/// ZERO := λf.λa.a = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::stumpfu::numerals::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_stumpfu());
/// ```
pub fn zero() -> Term { abs!(2, Var(1)) }

/// Produces a Stump-Fu-encoded number one.
///
/// ONE := λf.λa.f CHURCH_ONE ZERO = λ λ 2 CHURCH_ONE ZERO
///
/// # Example
/// ```
/// use lambda_calculus::stumpfu::numerals::one;
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
/// use lambda_calculus::stumpfu::numerals::succ;
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

/// Applied to two Stump-Fu-encoded numbers it produces their sum.
///
/// ADD := λnm.n (λcp.c SUCC m) m = λ λ 2 (λ λ 2 SUCC 3) 1
///
/// # Example
/// ```
/// use lambda_calculus::stumpfu::numerals::add;
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

impl IntoStumpFu for usize {
    fn into_stumpfu(self) -> Term {
        let mut ret = zero();

        for n in 1..self+1 {
            ret = abs!(2, app!(Var(2), n.into_church(), ret));
        }

        ret
    }
}
