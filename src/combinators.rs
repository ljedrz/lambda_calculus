//! [Standard terms](https://en.wikipedia.org/wiki/Lambda_calculus#Standard_terms) and
//! [combinators](https://en.wikipedia.org/wiki/Combinatory_logic#Combinatory_calculi)
//!
//! * [SKI](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
//! * [Iota](https://en.wikipedia.org/wiki/Iota_and_Jot)
//! * [BCKW](https://en.wikipedia.org/wiki/B,_C,_K,_W_system)
//! * the self-application combinator ω
//! * the divergent combinator Ω
//! * [the fixed-point combinators Y and Z](https://en.wikipedia.org/wiki/Fixed-point_combinator)
//! * the reverse application (thrush) combinator R

#![allow(non_snake_case)]

use crate::term::{Term, abs, app};
use crate::term::Term::*;

/// I - the identity combinator.
///
/// I ≡ λx.x ≡ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::I;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(I(), Var(1)), NOR, 0), Var(1));
/// assert_eq!(beta(app(I(), abs(Var(1))), NOR, 0), abs(Var(1)));
/// ```
pub fn I() -> Term { abs(Var(1)) }

/// K - the constant / discarding combinator; equivalent to `boolean::tru`.
///
/// K ≡ λxy.x ≡ λ λ 2 ≡ TRUE
///
/// # Example
/// ```
/// use lambda_calculus::combinators::K;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(K(), Var(1), Var(2)), NOR, 0), Var(1));
/// assert_eq!(beta(app!(K(), Var(2), Var(1)), NOR, 0), Var(2));
/// ```
pub fn K() -> Term { abs!(2, Var(2)) }

/// S - the substitution combinator.
///
/// S ≡ λxyz.x z (y z) ≡ λ λ λ 3 1 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::combinators::S;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(S(), Var(1), Var(2), Var(3)), NOR, 0),
///     app!(Var(1), Var(3), app(Var(2), Var(3)))
/// );
/// ```
pub fn S() -> Term {
    abs!(3, app!(Var(3), Var(1), app(Var(2), Var(1))))
}

/// Iota - the universal combinator.
///
/// i ≡ λx.x S K ≡ λ 1 S K
///
/// # Example
/// ```
/// use lambda_calculus::combinators::{i, I, K, S};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(i(), i()), NOR, 0), I());
/// assert_eq!(beta(app(i(), app(i(), app(i(), i()))), NOR, 0), K());
/// assert_eq!(beta(app(i(), app(i(), app(i(), app(i(), i())))), NOR, 0), S());
/// ```
pub fn i() -> Term { abs(app!(Var(1), S(), K())) }

/// B - the composition combinator.
///
/// B ≡ λxyz.x (y z) ≡ λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::combinators::B;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(B(), Var(1), Var(2), Var(3)), NOR, 0),
///     app(Var(1), app(Var(2), Var(3)))
/// );
/// ```
pub fn B() -> Term {
    abs!(3, app(Var(3), app(Var(2), Var(1))))
}

/// C - the swapping combinator.
///
/// C ≡ λxyz.x z y ≡ λ λ λ 3 1 2
///
/// # Example
/// ```
/// use lambda_calculus::combinators::C;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(C(), Var(1), Var(2), Var(3)), NOR, 0),
///     app!(Var(1), Var(3), Var(2))
/// );
/// ```
pub fn C() -> Term {
    abs!(3, app!(Var(3), Var(1), Var(2)))
}

/// W - the duplicating combinator.
///
/// W ≡ λxy.x y y ≡ λ λ 2 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::W;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(W(), Var(1), Var(2)), NOR, 0),
///     app!(Var(1), Var(2), Var(2))
/// );
/// ```
pub fn W() -> Term {
    abs!(2, app!(Var(2), Var(1), Var(1)))
}

/// ω - the self-application combinator.
///
/// ω ≡ λx.x x ≡ λ 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::o;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(o(), Var(1)), NOR, 0),
///     app(Var(1), Var(1))
/// );
/// ```
pub fn o() -> Term { abs(app(Var(1), Var(1))) }

/// Ω - the divergent combinator.
///
/// Ω ≡ ω ω
///
/// # Example
/// ```
/// use lambda_calculus::combinators::O;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(O(), NOR, 3), O()); // 3 β-reductions do nothing
/// ```
pub fn O() -> Term { app(o(), o()) }

/// Y - the lazy fixed-point combinator.
///
/// It is suitable for `NOR` (normal), `HNO` (hybrid normal), `CBN` (call-by-name) and `HSP`
/// (head spine) reduction `Order`s.
///
/// Y ≡ λf.(λx.f (x x)) (λx.f (x x)) ≡ λ (λ 2 (1 1)) (λ 2 (1 1))
///
/// # Example
/// ```
/// use lambda_calculus::combinators::Y;
/// use lambda_calculus::*;
///
/// fn dummy() -> Term { abs(Var(2)) } // a dummy term that won't easily reduce
///
/// assert_eq!(
///     beta(app(Y(), dummy()), NOR, 0),
///     beta(app(dummy(), app(Y(), dummy())), NOR, 0)
/// );
/// ```
pub fn Y() -> Term {
    abs(app(
        abs(app(Var(2), app(Var(1), Var(1)))),
        abs(app(Var(2), app(Var(1), Var(1))))
    ))
}

/// Z - the strict fixed-point combinator.
///
/// It will work with all the reduction orders suitable for its lazy counterpart (the `Y`
/// combinator). In addition, it will also work with `CBV` (call-by-value) and `HAP` (hybrid
/// applicative) reduction `Order`s, though it is not a drop-in replacement - in order for such
/// expressions to work, they need to be modified so that the evaluation of arguments of conditionals
/// and other terms that need to be lazy is delayed.
///
/// Z ≡ λf.(λx.f (λv.x x v)) (λx.f (λv.x x v)) ≡ λ (λ 2 (λ 2 2 1)) (λ 2 (λ 2 2 1))
///
/// # Example
/// ```
/// use lambda_calculus::combinators::Z;
/// use lambda_calculus::*;
///
/// fn dummy() -> Term { abs(Var(2)) } // a dummy term that won't easily reduce
///
/// assert_eq!(
///     beta(app(Z(), dummy()), CBV, 0),
///     beta(app(dummy(), app(Z(), dummy())), CBV, 0)
/// );
/// ```
pub fn Z() -> Term {
    abs(app(
        abs(app(Var(2), abs(app!(Var(2), Var(2), Var(1))))),
        abs(app(Var(2), abs(app!(Var(2), Var(2), Var(1)))))
    ))
}

/// R - the reverse application (thrush) combinator.
///
/// R ≡ λxf.f x ≡ λ λ 1 2
///
/// # Example
/// ```
/// use lambda_calculus::combinators::R;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(R(), Var(1), Var(2)), NOR, 0),
///     app(Var(2), Var(1))
/// );
/// ```
pub fn R() -> Term {
    abs!(2, app(Var(1), Var(2)))
}

/// Θ - Turing's fixed-point combinator
///
/// Θ ≡ (λxy.y (x x y)) (λxy.y (x x y)) ≡ (λ λ 1 (2 2 1)) (λ λ 1 (2 2 1))
///
/// It is suitable for `NOR` (normal), `HNO` (hybrid normal), `CBN` (call-by-name), and `HSP` (head
/// spine) reduction `Order`s.
///
/// # Example
/// ```
/// use lambda_calculus::combinators::T;
/// use lambda_calculus::*;
///
/// fn dummy() -> Term { abs(Var(2)) } // a dummy term that won't easily reduce
///
/// assert_eq!(
///     beta(app(T(), dummy()), NOR, 0),
///     beta(app(dummy(), app(T(), dummy())), NOR, 0)
/// );
/// ```
pub fn T() -> Term {
    app(
        abs!(2, app(Var(1), app!(Var(2), Var(2), Var(1)))),
        abs!(2, app(Var(1), app!(Var(2), Var(2), Var(1))))
    )
}
