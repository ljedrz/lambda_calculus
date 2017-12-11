//! [Standard terms](https://en.wikipedia.org/wiki/Lambda_calculus#Standard_terms) and
//! [combinators](https://en.wikipedia.org/wiki/Combinatory_logic#Combinatory_calculi)
//!
//! * [SKI](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
//! * [Iota](https://en.wikipedia.org/wiki/Iota_and_Jot)
//! * [BCKW](https://en.wikipedia.org/wiki/B,_C,_K,_W_system)
// //! * the recursion combinator U - needs more research
//! * the self-application combinator ω
//! * the divergent combinator Ω
//! * [the fixed-point combinators Y and Z](https://en.wikipedia.org/wiki/Fixed-point_combinator)
//! * the reverse application combinator T

use term::{Term, abs, app};
use term::Term::*;

/// I - the identity combinator.
///
/// I := λx.x = λ 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::i;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(i(), Var(1)), NOR, 0, false), Var(1));
/// assert_eq!(beta(app(i(), abs(Var(1))), NOR, 0, false), abs(Var(1)));
/// ```
pub fn i() -> Term { abs(Var(1)) }

/// K - the constant / discarding combinator.
///
/// K := λxy.x = λ λ 2 = TRUE
///
/// # Example
/// ```
/// use lambda_calculus::combinators::k;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(k(), Var(1), Var(2)), NOR, 0, false), Var(1));
/// assert_eq!(beta(app!(k(), Var(2), Var(1)), NOR, 0, false), Var(2));
/// ```
pub fn k() -> Term { abs!(2, Var(2)) }

/// S - the substitution combinator.
///
/// S := λxyz.x z (y z) = λ λ λ 3 1 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::combinators::s;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(s(), Var(1), Var(2), Var(3)), NOR, 0, false),
///     app!(Var(1), Var(3), app(Var(2), Var(3)))
/// );
/// ```
pub fn s() -> Term {
    abs!(3, app!(Var(3), Var(1), app(Var(2), Var(1))))
}

/// Iota - the universal combinator.
///
/// ι := λx.x S K = λ 1 S K
///
/// # Example
/// ```
/// use lambda_calculus::combinators::{iota, i, k, s};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(iota(), iota()), NOR, 0, false), i());
/// assert_eq!(beta(app(iota(), app(iota(), app(iota(), iota()))), NOR, 0, false), k());
/// assert_eq!(beta(app(iota(), app(iota(), app(iota(), app(iota(), iota())))), NOR, 0, false), s());
/// ```
pub fn iota() -> Term { abs(app!(Var(1), s(), k())) }

/// B - the composition combinator.
///
/// B := λxyz.x (y z) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::combinators::b;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(b(), Var(1), Var(2), Var(3)), NOR, 0, false),
///     app(Var(1), app(Var(2), Var(3)))
/// );
/// ```
pub fn b() -> Term {
    abs!(3, app(Var(3), app(Var(2), Var(1))))
}

/// C - the swapping combinator.
///
/// C := λxyz.x z y = λ λ λ 3 1 2
///
/// # Example
/// ```
/// use lambda_calculus::combinators::c;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(c(), Var(1), Var(2), Var(3)), NOR, 0, false),
///     app!(Var(1), Var(3), Var(2))
/// );
/// ```
pub fn c() -> Term {
    abs!(3, app!(Var(3), Var(1), Var(2)))
}

/// W - the duplicating combinator.
///
/// W := λxy.x y y = λ λ 2 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::w;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(w(), Var(1), Var(2)), NOR, 0, false),
///     app!(Var(1), Var(2), Var(2))
/// );
/// ```
pub fn w() -> Term {
    abs!(2, app!(Var(2), Var(1), Var(1)))
}
/*
/// U - the recursion combinator.
///
/// U := λxy.y (x x y) = λ λ 1 (2 2 1)
pub fn u() -> Term { abs!(2, app(Var(1), app!(Var(2), Var(2), Var(1)))) }
*/
/// ω - the self-application combinator.
///
/// ω := λx.x x = λ 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::om;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(om(), Var(1)), NOR, 0, false),
///     app(Var(1), Var(1))
/// );
/// ```
pub fn om() -> Term { abs(Var(1).app(Var(1))) }

/// Ω - the divergent combinator.
///
/// Ω := ω ω
///
/// # Example
/// ```
/// use lambda_calculus::combinators::omm;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(omm(), NOR, 3, false), omm()); // 3 β-reductions do nothing
/// ```
pub fn omm() -> Term { om().app(om()) }

/// Y - the lazy fixed-point combinator.
///
/// It is suitable for `NOR` (normal), `HNO` (hybrid normal), `CBN` (call-by-name) and `HSP`
/// (head spine) reduction `Order`s.
///
/// Y := λf.(λx.f (x x)) (λx.f (x x)) = λ (λ 2 (1 1)) (λ 2 (1 1))
///
/// # Example
/// ```
/// use lambda_calculus::combinators::y;
/// use lambda_calculus::*;
///
/// fn dummy() -> Term { abs(Var(2)) } // a dummy term that won't easily reduce
///
/// assert_eq!(
///     beta(app(y(), dummy()), NOR, 0, false),
///     beta(app(dummy(), app(y(), dummy())), NOR, 0, false)
/// );
/// ```
pub fn y() -> Term {
    abs(app(
        abs(app(Var(2), app(Var(1), Var(1)))),
        abs(app(Var(2), app(Var(1), Var(1))))
    ))
}

/// Z - the strict fixed-point combinator.
///
/// It will work with all the reduction orders suitable for its lazy counterpart (the `Y`
/// combinator). In addition, it will also work with `CBV` (call-by-value) and `HAP` (hybrid
/// applicative) reduction `Order`s, but with them it's not a drop-in replacement for the `Y`
/// combinator - in order for such expressions to work, they need to be modified so that the
/// evaluation of arguments of conditionals and other terms that need to be lazy is delayed.
///
/// Z := λf.(λx.f (λv.x x v)) (λx.f (λv.x x v)) = λ (λ 2 (λ 2 2 1)) (λ 2 (λ 2 2 1))
///
/// # Example
/// ```
/// use lambda_calculus::combinators::z;
/// use lambda_calculus::*;
///
/// fn dummy() -> Term { abs(Var(2)) } // a dummy term that won't easily reduce
///
/// assert_eq!(
///     beta(app(z(), dummy()), CBV, 0, false),
///     beta(app(dummy(), app(z(), dummy())), CBV, 0, false)
/// );
/// ```
pub fn z() -> Term {
    abs(app(
        abs(app(Var(2), abs(app!(Var(2), Var(2), Var(1))))),
        abs(app(Var(2), abs(app!(Var(2), Var(2), Var(1)))))
    ))
}

/// T - the reverse application combinator.
///
/// T := λxf. f x = λ λ 1 2
///
/// # Example
/// ```
/// use lambda_calculus::combinators::t;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(t(), Var(1), Var(2)), NOR, 0, false),
///     app(Var(2), Var(1))
/// );
/// ```
pub fn t() -> Term {
    abs!(2, app(Var(1), Var(2)))
}
