//! [Parigot numerals](https://ir.uiowa.edu/cgi/viewcontent.cgi?article=5357&context=etd)

use term::{Term, abs, app};
use term::Term::*;
use parigot::convert::IntoParigot;

/// Produces a Parigot-encoded number zero.
///
/// ZERO := λsz.z = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_parigot());
/// ```
pub fn zero() -> Term { abs!(2, Var(1)) }

/// Produces a Parigot-encoded number one.
///
/// ONE := λsz.s ZERO z = λ λ 2 ZERO 1
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_parigot());
/// ```
pub fn one() -> Term { abs!(2, app!(Var(2), zero(), Var(1))) }

/// Applied to a Parigot-encoded number it produces its successor.
///
/// SUCC := λnsz.s n (n s z) = λ λ λ 2 3 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_parigot()), NOR, 0), 1.into_parigot());
/// assert_eq!(beta(app(succ(), 1.into_parigot()), NOR, 0), 2.into_parigot());
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
/// assert_eq!(beta(app(pred(), 1.into_parigot()), NOR, 0), 0.into_parigot());
/// assert_eq!(beta(app(pred(), 3.into_parigot()), NOR, 0), 2.into_parigot());
/// ```
pub fn pred() -> Term {
    abs(app!(Var(1), abs!(2, Var(2)), zero()))
}

/// Applied to two Parigot-encoded numbers it produces their sum.
///
/// PLUS := λnm.n (λp.SUCC) m = λ λ 2 (λ SUCC) 1
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::plus;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(plus(), 1.into_parigot(), 2.into_parigot()), NOR, 0), 3.into_parigot());
/// assert_eq!(beta(app!(plus(), 2.into_parigot(), 3.into_parigot()), NOR, 0), 5.into_parigot());
/// ```
pub fn plus() -> Term {
    abs!(2, app!(Var(2), abs(succ()), Var(1)))
}

/// Applied to two Parigot-encoded numbers it yields their product.
///
/// MULT := λnm.n (λp.PLUS m) ZERO = λ λ 2 (λ PLUS 2) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::parigot::numerals::mult;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(mult(), 1.into_parigot(), 2.into_parigot()), NOR, 0), 2.into_parigot());
/// assert_eq!(beta(app!(mult(), 2.into_parigot(), 3.into_parigot()), NOR, 0), 6.into_parigot());
/// ```
pub fn mult() -> Term {
    abs!(2, app!(Var(2), abs(app(plus(), Var(2))), zero()))
}

impl IntoParigot for usize {
    fn into_parigot(self) -> Term {
        let mut ret = zero();

        for _ in 0..self {
            ret = abs!(2, app!(Var(2), ret.clone(), ret.unabs().and_then(|r| r.unabs()).unwrap()));
        }

        ret
    }
}
