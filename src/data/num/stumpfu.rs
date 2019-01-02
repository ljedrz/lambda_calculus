//! [Stump-Fu numerals](http://homepage.cs.uiowa.edu/~astump/papers/stump-fu-jfp-2016.pdf)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::num::convert::IntoChurchNum;
use crate::data::boolean::{tru, fls};
use crate::data::num::{church, scott, parigot};

/// Produces a Stump-Fu-encoded number zero; equivalent to `boolean::fls`.
///
/// ZERO ≡ λf.λa.a ≡ λ λ 1 ≡ FALSE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_stumpfu());
/// ```
pub fn zero() -> Term { fls() }

/// Applied to a Stump-Fu-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO ≡ λn.n (λxy.FALSE) TRUE ≡ λ 1 (λ λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::is_zero;
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
/// ONE ≡ λf.λa.f CHURCH_ONE ZERO ≡ λ λ 2 CHURCH_ONE ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_stumpfu());
/// ```
pub fn one() -> Term { abs!(2, app!(Var(2), 1.into_church(), zero())) }

/// Applied to a Stump-Fu-encoded number it produces its successor.
///
/// SUCC ≡ λn.n (λcpfa.f (CHURCH_SUCC c) n) ONE ≡ λ 1 (λ λ λ λ 2 (CHURCH_SUCC 4) 5) ONE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::succ;
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
/// PRED ≡ λn.n (λcs.s) ZERO ≡ λ 1 (λ λ 1) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::pred;
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
/// ADD ≡ λnm.n (λcp.c SUCC m) m ≡ λ λ 2 (λ λ 2 SUCC 3) 1
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::add;
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

/// Applied to two Stump-Fu-encoded numbers it produces their product.
///
/// MUL ≡ λnm.n (λcp.c (λx.ADD m x) ZERO) ZERO ≡ λ λ 2 (λ λ 2 (λ ADD 4 1) ZERO) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::mul;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(mul(), 1.into_stumpfu(), 2.into_stumpfu()), NOR, 0), 2.into_stumpfu());
/// assert_eq!(beta(app!(mul(), 2.into_stumpfu(), 3.into_stumpfu()), NOR, 0), 6.into_stumpfu());
/// ```
pub fn mul() -> Term {
    abs!(2, app!(
        Var(2),
        abs!(2, app!(
            Var(2),
            abs(app!(add(), Var(4), Var(1))),
            zero()
        )),
        zero()
    ))
}

/// Applied to a Stump-Fu-encoded number it produces the equivalent Church-encoded number.
///
/// TO_CHURCH ≡ λn.n TRUE n ≡ λ 1 TRUE 1
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::to_church;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_church(), 0.into_stumpfu()), NOR, 0), 0.into_church());
/// assert_eq!(beta(app(to_church(), 1.into_stumpfu()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(to_church(), 4.into_stumpfu()), NOR, 0), 4.into_church());
/// ```
pub fn to_church() -> Term {
    abs(app!(
        Var(1),
        tru(),
        Var(1)
    ))
}

/// Applied to a Stump-Fu-encoded number it produces the equivalent Scott-encoded number.
///
/// TO_SCOTT ≡ λn.(λm.m SCOTT_SUCC SCOTT_ZERO) (n TRUE n)
///          ≡ λ (λ 1 SCOTT_SUCC SCOTT_ZERO) (1 TRUE 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::to_scott;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_scott(), 0.into_stumpfu()), NOR, 0), 0.into_scott());
/// assert_eq!(beta(app(to_scott(), 1.into_stumpfu()), NOR, 0), 1.into_scott());
/// assert_eq!(beta(app(to_scott(), 4.into_stumpfu()), NOR, 0), 4.into_scott());
/// ```
pub fn to_scott() -> Term {
    abs(app(
        abs(app!(
            Var(1),
            scott::succ(),
            scott::zero()
        )),
        app!(
            Var(1),
            tru(),
            Var(1)
        )
    ))
}

/// Applied to a Stump-Fu-encoded number it produces the equivalent Parigot-encoded number.
///
/// TO_PARIGOT ≡ λn.(λm.m PARIGOT_SUCC PARIGOT_ZERO) (n TRUE n)
///            ≡ λ (λ 1 PARIGOT_SUCC PARIGOT_ZERO) (1 TRUE 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::stumpfu::to_parigot;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_parigot(), 0.into_stumpfu()), NOR, 0), 0.into_parigot());
/// assert_eq!(beta(app(to_parigot(), 1.into_stumpfu()), NOR, 0), 1.into_parigot());
/// assert_eq!(beta(app(to_parigot(), 4.into_stumpfu()), NOR, 0), 4.into_parigot());
/// ```
pub fn to_parigot() -> Term {
    abs(app(
        abs(app!(
            Var(1),
            parigot::succ(),
            parigot::zero()
        )),
        app!(
            Var(1),
            tru(),
            Var(1)
        )
    ))
}
