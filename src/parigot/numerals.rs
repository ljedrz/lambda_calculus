//! [Parigot numerals](https://ir.uiowa.edu/cgi/viewcontent.cgi?article=5357&context=etd)

use term::{Term, abs};
use term::Term::*;

/// Produces a Parigot-encoded number zero.
///
/// ZERO := λsz.z = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into());
/// ```
pub fn zero() -> Term { abs!(2, Var(1)) }

/// Applied to a Parigot-encoded number it produces its successor.
///
/// SUCC := λnsz.s n (n s z) = λ λ λ 2 3 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into()), NOR, 0, false), 1.into());
/// assert_eq!(beta(app(succ(), 1.into()), NOR, 0, false), 2.into());
/// ```
pub fn succ() -> Term {
    abs!(3, app!(Var(2), Var(3), app!(Var(3), Var(2), Var(1))))
}

/// Applied to a Parigot-encoded number it produces its predecessor.
///
/// PRED := λn.n (λxy.y) ZERO  = λ 1 (λ λ 1) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into()), NOR, 0, false), 0.into());
/// assert_eq!(beta(app(pred(), 3.into()), NOR, 0, false), 2.into());
/// ```
pub fn pred() -> Term {
    abs(app!(Var(1), abs!(2, Var(2)), zero()))
}

/// Applied to two Parigot-encoded numbers it produces their sum.
///
/// PLUS := λnm.n (λx.SUCC) m = λ λ 2 (λ SUCC) 1
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::plus;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(plus(), 1.into(), 2.into()), NOR, 0, false), 3.into());
/// assert_eq!(beta(app!(plus(), 2.into(), 3.into()), NOR, 0, false), 5.into());
/// ```
pub fn plus() -> Term {
    abs!(2, app!(Var(2), abs(succ()), Var(1)))
}

impl From<usize> for Term {
    fn from(n: usize) -> Self {
        let mut ret = zero();

        for _ in 0..n {
            ret = abs!(2, app!(Var(2), ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}
