//! [Scott numerals](http://lucacardelli.name/Papers/Notes/scott2.pdf)

use term::{Term, abs, app};
use term::Term::*;
use data::numerals::convert::IntoScott;

/// Produces a Scott-encoded number zero.
///
/// ZERO := λxy.x = λ λ 2
///
/// # Example
/// ```
/// use lambda_calculus::scott::numerals::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_scott());
/// ```
pub fn zero() -> Term { abs!(2, Var(2)) }

/// Applied to a Scott-encoded number it produces its successor.
///
/// SUCC := λnxy.y n = λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::scott::numerals::succ;
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
/// use lambda_calculus::scott::numerals::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into_scott()), NOR, 0), 0.into_scott());
/// assert_eq!(beta(app(pred(), 3.into_scott()), NOR, 0), 2.into_scott());
/// ```
pub fn pred() -> Term {
    abs(app!(Var(1), zero(), abs(Var(1))))
}

impl IntoScott for usize {
    fn into_scott(self) -> Term {
        let mut ret = abs!(2, Var(2));

        for _ in 0..self {
            ret = abs!(2, app(Var(1), ret));
        }

        ret
    }
}
