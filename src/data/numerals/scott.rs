//! [Scott numerals](http://lucacardelli.name/Papers/Notes/scott2.pdf)

use data::boolean::{tru, fls};
use term::{Term, abs, app};
use term::Term::*;

/// Produces a Scott-encoded number zero.
///
/// ZERO := λxy.x = λ λ 2
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::scott::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_scott());
/// ```
pub fn zero() -> Term { abs!(2, Var(2)) }

/// Applied to a Scott-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO := λn.n TRUE (λx.FALSE) =  λ 1 TRUE (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::scott::is_zero;
/// use lambda_calculus::data::boolean::{tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_zero(), 0.into_scott()), NOR, 0), tru());
/// assert_eq!(beta(app(is_zero(), 1.into_scott()), NOR, 0), fls());
/// ```
pub fn is_zero() -> Term {
    abs(app!(Var(1), tru(), abs(fls())))
}

/// Applied to a Scott-encoded number it produces its successor.
///
/// SUCC := λnxy.y n = λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::scott::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_scott()), NOR, 0), 1.into_scott());
/// assert_eq!(beta(app(succ(), 1.into_scott()), NOR, 0), 2.into_scott());
/// ```
pub fn succ() -> Term {
    abs!(3, app(Var(1), Var(3)))
}

/// Applied to a Scott-encoded number it produces its predecessor.
///
/// PRED := λn.n ZERO (λx.x) = λ 1 ZERO (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::scott::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into_scott()), NOR, 0), 0.into_scott());
/// assert_eq!(beta(app(pred(), 3.into_scott()), NOR, 0), 2.into_scott());
/// ```
pub fn pred() -> Term {
    abs(app!(Var(1), zero(), abs(Var(1))))
}
