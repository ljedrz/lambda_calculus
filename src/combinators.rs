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

use term::*;
use term::Term::*;

/// I - the identity combinator.
///
/// I := λx.x = λ 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::i;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(i().app(zero())), zero());
/// ```
pub fn i() -> Term { abs(Var(1)) }

/// K - the constant / discarding combinator.
///
/// K := λxy.x = λ λ 2 = true
///
/// # Example
/// ```
/// use lambda_calculus::combinators::k;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(k().app(zero()).app(one())), zero());
/// ```
pub fn k() -> Term { abs(abs(Var(2))) }

/// S - the substitution combinator.
///
/// S := λxyz.x z (y z) = λ λ λ 3 1 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::s;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(s().app(0.into()).app(1.into()).app(2.into())),
///            normalize(Term::from(0).app(2.into()).app(Term::from(1).app(2.into()))));
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
/// use lambda_calculus::combinators::{iota, i, k, s};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(iota().app(iota())), i());
/// assert_eq!(normalize(iota().app(iota().app(iota().app(iota())))), k());
/// assert_eq!(normalize(iota().app(iota().app(iota().app(iota().app(iota()))))), s());
/// ```
pub fn iota() -> Term { abs(Var(1).app(s()).app(k())) }

/// B - the composition combinator.
///
/// B := λxyz.x (y z) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::b;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(b().app(0.into()).app(1.into()).app(2.into())),
///            normalize(Term::from(0).app(Term::from(1).app(2.into()))));
/// ```
pub fn b() -> Term {
    abs(abs(abs(
        Var(3)
        .app(Var(2).app(Var(1)))
    )))
}

/// C - the swapping combinator.
///
/// C := λxyz.x z y = λ λ λ 3 1 2
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::combinators::c;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(c().app(0.into()).app(1.into()).app(2.into())),
///            normalize(Term::from(0).app(2.into()).app(1.into())));
/// ```
pub fn c() -> Term {
    abs(abs(abs(
        Var(3)
        .app(Var(1))
        .app(Var(2))
    )))
}

/// W - the duplicating combinator.
///
/// W := λxy.x y y = λ λ 2 1 1
///
/// # Example
/// ```
/// use lambda_calculus::combinators::w;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(w().app(zero()).app(one())),
///            normalize(zero().app(one()).app(one())));
/// ```
pub fn w() -> Term {
    abs(abs(
        Var(2)
        .app(Var(1))
        .app(Var(1))
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
/// ω := λx.x x
/// # Example
///
/// ```
/// use lambda_calculus::combinators::om;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(om().app(zero())), normalize(zero().app(zero())));
/// ```
pub fn om() -> Term { abs(Var(1).app(Var(1))) }

/// Ω - the divergent combinator.
///
/// Ω := ω ω
///
/// # Example
///
/// ```
/// use lambda_calculus::combinators::omm;
///
/// let mut doesnt_reduce = omm();
///
/// doesnt_reduce.beta_reduce();
///
/// assert_eq!(doesnt_reduce, omm());
/// ```
pub fn omm() -> Term { om().app(om()) }

/// Y - the fixed-point combinator.
///
/// Y := λg.(λx.g (x x)) (λx.g (x x)) = λ (λ 2 (1 1)) (λ 2 (1 1))
/// # Example
///
/// ```
/// use lambda_calculus::combinators::y;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(y().app(zero())), normalize(zero().app(y().app(zero()))));
/// ```
pub fn y() -> Term {
    abs(app(
        abs(Var(2).app(Var(1).app(Var(1)))),
        abs(Var(2).app(Var(1).app(Var(1))))
    ))
}
