//! [Lambda-encoded pair](https://en.wikipedia.org/wiki/Church_encoding#Church_pairs)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls};

/// Applied to two `Term`s it contains them in a lambda-encoded pair.
///
/// PAIR ≡ λxyz.z x y ≡ λ λ λ 1 3 2
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::pair;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(pair(), 1.into_church(), 2.into_church()), NOR, 0),
///     (1, 2).into_church()
/// );
/// ```
pub fn pair() -> Term {
    abs!(3, app!(Var(1), Var(3), Var(2)))
}

/// Applied to a lambda-encoded pair `(a, b)` it yields `a`.
///
/// FST ≡ λp.p TRUE ≡ λ 1 TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::fst;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(fst(), (1, 2).into_church()), NOR, 0),
///     1.into_church()
/// );
/// ```
pub fn fst() -> Term { abs(app(Var(1), tru())) }

/// Applied to a lambda-encoded pair `(a, b)` it yields `b`.
///
/// SND ≡ λp.p FALSE ≡ λ 1 FALSE
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::snd;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(snd(), (1, 2).into_church()), NOR, 0),
///     2.into_church()
/// );
/// ```
pub fn snd() -> Term { abs(app(Var(1), fls())) }

/// Applied to a function and a lambda-encoded pair `(a, b)` it uncurries it
/// and applies the function to `a` and then `b`.
///
/// UNCURRY ≡ λfp.f (FST p) (SND p) ≡ λ λ 2 (FST 1) (SND 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::uncurry;
/// use lambda_calculus::data::num::church::add;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(uncurry(), add(), (1, 2).into_church()), NOR, 0),
///     3.into_church()
/// );
/// ```
pub fn uncurry() -> Term {
    abs!(2, app!(
        Var(2),
        app(fst(), Var(1)),
        app(snd(), Var(1))
    ))
}

/// Applied to a function and two arguments `a` and `b`, it applies the function to the
/// lambda-encoded pair `(a, b)`.
///
/// CURRY ≡ λfab.f (PAIR a b) ≡ λ λ λ 3 (PAIR 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::{fst, curry};
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(curry(), fst(), 1.into_church(), 2.into_church()), NOR, 0),
///     1.into_church()
/// );
/// ```
pub fn curry() -> Term {
    abs!(3, app(
        Var(3),
        app!(pair(), Var(2), Var(1))
    ))
}

/// Applied to a lambda-encoded pair `(a, b)` it swaps its elements so that it becomes `(b, a)`.
///
/// SWAP ≡ λp.PAIR (SND p) (FST p) ≡ λ PAIR (SND 1) (FST 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::pair::swap;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(swap(), (1, 2).into_church()), NOR, 0),
///     (2, 1).into_church()
/// );
/// ```
pub fn swap() -> Term {
    abs(app!(
        pair(),
        app(snd(), Var(1)),
        app(fst(), Var(1))
    ))
}

impl Into<Term> for (Term, Term) {
    fn into(self) -> Term {
        abs(app!(Var(1), self.0, self.1))
    }
}
