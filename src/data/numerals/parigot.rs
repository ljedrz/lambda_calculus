//! [Parigot numerals](https://ir.uiowa.edu/cgi/viewcontent.cgi?article=5357&context=etd)

use term::{Term, abs, app};
use term::Term::*;
use data::numerals::convert::IntoParigot;

/// Produces a Parigot-encoded number zero.
///
/// ZERO := λsz.z = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::parigot::zero;
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
/// use lambda_calculus::data::numerals::parigot::one;
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
/// use lambda_calculus::data::numerals::parigot::succ;
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
/// use lambda_calculus::data::numerals::parigot::pred;
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
/// ADD := λnm.n (λp.SUCC) m = λ λ 2 (λ SUCC) 1
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::parigot::add;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(add(), 1.into_parigot(), 2.into_parigot()), NOR, 0), 3.into_parigot());
/// assert_eq!(beta(app!(add(), 2.into_parigot(), 3.into_parigot()), NOR, 0), 5.into_parigot());
/// ```
pub fn add() -> Term {
    abs!(2, app!(Var(2), abs(succ()), Var(1)))
}

/// Applied to two Parigot-encoded numbers it yields their product.
///
/// MULT := λnm.n (λp.ADD m) ZERO = λ λ 2 (λ ADD 2) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::parigot::mult;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(mult(), 1.into_parigot(), 2.into_parigot()), NOR, 0), 2.into_parigot());
/// assert_eq!(beta(app!(mult(), 2.into_parigot(), 3.into_parigot()), NOR, 0), 6.into_parigot());
/// ```
pub fn mult() -> Term {
    abs!(2, app!(Var(2), abs(app(add(), Var(2))), zero()))
}

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// SUB := λnm.m (λp. PRED) n = λ λ 1 (λ PRED) 2
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::parigot::sub;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(sub(), 1.into_parigot(), 0.into_parigot()), NOR, 0), 1.into_parigot());
/// assert_eq!(beta(app!(sub(), 3.into_parigot(), 1.into_parigot()), NOR, 0), 2.into_parigot());
/// assert_eq!(beta(app!(sub(), 5.into_parigot(), 2.into_parigot()), NOR, 0), 3.into_parigot());
/// ```
pub fn sub() -> Term {
    abs!(2, app!(Var(1), abs(pred()), Var(2)))
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
