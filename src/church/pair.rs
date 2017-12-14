//! [Church pairs](https://en.wikipedia.org/wiki/Church_encoding#Church_pairs)

use term::{Term, abs, app};
use term::Term::*;
use church::boolean::{tru, fls};
use church::conversions::IntoChurch;

/// Produces a Church-encoded pair; applying it to two other terms puts them inside it.
///
/// PAIR := λxyz.z x y = λ λ λ 1 3 2
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::pair;
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

/// Applied to a Church-encoded pair `(a, b)` it yields `a`.
///
/// FST := λp.p TRUE = λ 1 TRUE
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::fst;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(fst(), (1, 2).into_church()), NOR, 0),
///     1.into_church()
/// );
/// ```
pub fn fst() -> Term { abs(app(Var(1), tru())) }

/// Applied to a Church-encoded pair `(a, b)` it yields `b`.
///
/// SND := λp.p FALSE = λ 1 FALSE
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::snd;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(snd(), (1, 2).into_church()), NOR, 0),
///     2.into_church()
/// );
/// ```
pub fn snd() -> Term { abs(app(Var(1), fls())) }

/// Applied to a function and a Church-encoded pair `(a, b)` it uncurries it
/// and applies the function to `a` and then `b`.
///
/// UNCURRY := λf.λp.f (FST p) (SND p) = λ λ 2 (FST 1) (SND 1)
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::uncurry;
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(uncurry(), plus(), (1, 2).into_church()), NOR, 0),
///     3.into_church()
/// );
/// ```
pub fn uncurry() -> Term {
    abs!(2, app!(
        Var(2),
        app(Var(1), tru()),
        app(Var(1), fls())
    ))
}

/// Applied to a function and two arguments `a` and `b`, it applies the function to the
/// Church-encoded pair `(a, b)`.
///
/// CURRY := λfab.f (PAIR a b) = λ λ λ 3 (PAIR 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::{fst, curry};
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
        abs(app!(Var(1), Var(3), Var(2)))
    ))
}

/// Applied to a Church-encoded pair `(a, b)` it swaps its elements so that it becomes `(b, a)`.
///
/// SWAP := λp.p PAIR (SND p) (FST p) = λ 1 PAIR (SND 1) (FST 1)
///
/// # Example
/// ```
/// use lambda_calculus::church::pair::swap;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(swap(), (1, 2).into_church()), NOR, 0), (2, 1).into_church());
/// ```
pub fn swap() -> Term {
    abs!(2, app!(
        Var(1),
        app(Var(2), abs!(2, Var(1))),
        app(Var(2), abs!(2, Var(2)))
    ))
}

impl IntoChurch for (Term, Term) {
    fn into_church(self) -> Term {
        abs(app!(Var(1), self.0, self.1))
    }
}

impl<T,U> IntoChurch for (T, U) where T:IntoChurch, U:IntoChurch {
    fn into_church(self) -> Term {
        abs(app!(Var(1), self.0.into_church(), self.1.into_church()))
    }
}
