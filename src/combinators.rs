//! [Standard terms](https://en.wikipedia.org/wiki/Lambda_calculus#Standard_terms) and
//! [combinators](https://en.wikipedia.org/wiki/Combinatory_logic#Combinatory_calculi)
//!
//! * [SKI](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
//! * [Iota](https://en.wikipedia.org/wiki/Iota_and_Jot)
//! * [BCKW](https://en.wikipedia.org/wiki/B,_C,_K,_W_system)
// //! * the recursion combinator U - needs more research
//! * the looping combinator ω
//! * the divergent combinator Ω
//! * [the fixed-point combinator Y](https://en.wikipedia.org/wiki/Fixed-point_combinator)
//! * the thrush (reverse application) combinator T

use term::*;
use term::Term::*;
use reduction::{EVALUATION_ORDER, Order};

/// I - the identity combinator.
///
/// I := λx.x = λ 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::i;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(i().app(zero())), zero());
/// ```
pub fn i() -> Term { abs(Var(1)) }

/// K - the constant / discarding combinator.
///
/// K := λxy.x = λ λ 2 = TRUE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::combinators::k;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(k(), zero(), one())), zero());
/// # }
/// ```
pub fn k() -> Term { abs(abs(Var(2))) }

/// S - the substitution combinator.
///
/// S := λxyz.x z (y z) = λ λ λ 3 1 (2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::s;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(s(), 0.into(), 1.into(), 2.into())),
///            beta_full(app!(Term::from(0), 2.into(), app!(Term::from(1), 2.into()))));
/// # }
/// ```
pub fn s() -> Term {
    abs(abs(abs(
        Var(3)
        .app(Var(1))
        .app(Var(2).app(Var(1)))
    )))
}

/// Iota - the universal combinator.
///
/// ι := λx.x S K = λ 1 S K
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::combinators::{iota, i, k, s};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(iota(), iota())), i());
/// assert_eq!(beta_full(app!(iota(), app!(iota(), app!(iota(), iota())))), k());
/// assert_eq!(beta_full(app!(iota(), app!(iota(), app!(iota(), app!(iota(), iota()))))), s());
/// # }
/// ```
pub fn iota() -> Term { abs(app!(Var(1), s(), k())) }

/// B - the composition combinator.
///
/// B := λxyz.x (y z) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::b;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(b(), 0.into(), 1.into(), 2.into())),
///            beta_full(app!(Term::from(0), app!(Term::from(1), 2.into()))));
/// # }
/// ```
pub fn b() -> Term {
    abs(abs(abs(
        app!(Var(3), app!(Var(2), Var(1)))
    )))
}

/// C - the swapping combinator.
///
/// C := λxyz.x z y = λ λ λ 3 1 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::c;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(c(), 0.into(), 1.into(), 2.into())),
///            beta_full(app!(Term::from(0), 2.into(), 1.into())));
/// # }
/// ```
pub fn c() -> Term {
    abs(abs(abs(
        app!(Var(3), Var(1), Var(2))
    )))
}

/// W - the duplicating combinator.
///
/// W := λxy.x y y = λ λ 2 1 1
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::combinators::w;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(w(), zero(), one())),
///            beta_full(app!(zero(), one(), one())));
/// # }
/// ```
pub fn w() -> Term {
    abs(abs(
        app!(Var(2), Var(1), Var(1))
    ))
}
/*
/// U - the recursion combinator.
///
/// U := λxy.y (x x y) = λ λ 1 (2 2 1)
pub fn u() -> Term { abs(abs(Var(1).app(Var(2).app(Var(2)).app(Var(1))))) }
*/
/// ω - the looping combinator.
///
/// ω := λx.x x = λ 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::om;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(om().app(zero())), beta_full(zero().app(zero())));
/// ```
pub fn om() -> Term { abs(Var(1).app(Var(1))) }

/// Ω - the divergent combinator.
///
/// Ω := ω ω
///
/// # Example
/// ```
/// use lambda_calculus::combinators::omm;
/// use lambda_calculus::reduction::beta_once;
///
/// assert_eq!(beta_once(omm()), omm());
/// ```
pub fn omm() -> Term { om().app(om()) }

/// Y - the fixed-point combinator; it has different variants depending on the evaluation order.
///
/// Y<sub>N, CBN</sub> := λf.(λx.f (x x)) (λx.f (x x)) = λ (λ 2 (1 1)) (λ 2 (1 1))
///
/// Y<sub>APP</sub> := N/A - the Y combinator won't work with applicative order
///
/// Y<sub>CBV</sub> := λf.(λx.f (λv.x x v)) (λx.f (λv.x x v)) = λ (λ 2 (λ 2 2 1)) (λ 2 (λ 2 2 1))
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::combinators::y;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(y().app(zero())), beta_full(app!(zero(), app!(y(), zero()))));
/// # }
/// ```
pub fn y() -> Term {
    match EVALUATION_ORDER {
        Order::Normal | Order::CallByName => {
            abs(app(
                abs(app!(Var(2), app!(Var(1), Var(1)))),
                abs(app!(Var(2), app!(Var(1), Var(1))))
            ))
        },
        Order::Applicative => {
            panic!("Y combinator doesn't work with applicative evaluation order")
        },
        Order::CallByValue => {
            abs(
                app!(
                    abs(app!(Var(2), abs(app!(Var(2), Var(2), Var(1))))),
                    abs(app!(Var(2), abs(app!(Var(2), Var(2), Var(1)))))
                )
            )
        }
    }
}

/// T - the thrush combinator
///
/// T := λxf. f x = λ λ 1 2
///
/// # Example
/// ```
/// use lambda_calculus::combinators::t;
/// use lambda_calculus::arithmetic::{zero, one};
///
/// assert_eq!(t().apply(&zero()).and_then(|t| t.apply(&one())), Ok(one().app(zero())));
/// ```
pub fn t() -> Term {
    abs(abs(
        app(Var(1), Var(2))
    ))
}
