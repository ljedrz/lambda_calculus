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
use reduction::{EVAL_ORDER, Order};

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
/// use lambda_calculus::combinators::k;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(k().app(zero()).app(one())), zero());
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(s().app(0.into()).app(1.into()).app(2.into())),
///            beta_full(Term::from(0).app(2.into()).app(Term::from(1).app(2.into()))));
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(iota().app(iota())), i());
/// assert_eq!(beta_full(iota().app(iota().app(iota().app(iota())))), k());
/// assert_eq!(beta_full(iota().app(iota().app(iota().app(iota().app(iota()))))), s());
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(b().app(0.into()).app(1.into()).app(2.into())),
///            beta_full(Term::from(0).app(Term::from(1).app(2.into()))));
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(c().app(0.into()).app(1.into()).app(2.into())),
///            beta_full(Term::from(0).app(2.into()).app(1.into())));
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(w().app(zero()).app(one())),
///            beta_full(zero().app(one()).app(one())));
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
///
/// let mut doesnt_reduce = omm();
///
/// doesnt_reduce.beta_once();
///
/// assert_eq!(doesnt_reduce, omm());
/// ```
pub fn omm() -> Term { om().app(om()) }

/// Y - the fixed-point combinator.
///
/// Y := λf.(λx.f (x x)) (λx.f (x x)) = λ (λ 2 (1 1)) (λ 2 (1 1))
///
/// # Example
/// ```
/// use lambda_calculus::combinators::y;
/// use lambda_calculus::arithmetic::zero;
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(y().app(zero())), beta_full(zero().app(y().app(zero()))));
/// ```
pub fn y() -> Term {
    match EVAL_ORDER {
        Order::Normal => {
            abs(app(
                abs(Var(2).app(Var(1).app(Var(1)))),
                abs(Var(2).app(Var(1).app(Var(1))))
            ))
        }
        Order::Applicative => { /* should any variant work with applicative order? */
            panic!("Y combinator won't work with applicative order")
            //parse(&"(λλ212)(λλ2(121))").unwrap()
            //parse(&"(λλ(1(λ3321)))(λλ(1(λ3321)))").unwrap()
            //parse(&"(λ11)(λ(λ(3(22)1)))").unwrap()
            //parse(&"λ(λ(2(λ(221))))(λ(2(λ(221))))").unwrap()
            //parse(&"λ(λ11)(λ(2(λ((22)1))))").unwrap()
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
