//! Church-encoded option type

use term::{Term, abs, app};
use term::Term::*;
use church::boolean::{tru, fls};
use church::conversions::IntoChurch;

/// Produces a Church-encoded empty option.
///
/// NONE := λns.n = λ λ 2
pub fn none() -> Term { tru() }

/// Applied to an argument it consumes it and produces a Church-encoded option that contains it.
///
/// SOME := λans.s a = λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::church::option::some;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(some(), 1.into_church()), NOR, 0), Some(1.into_church()).into_church());
/// ```
pub fn some() -> Term {
    abs!(3, app(Var(1), Var(3)))
}

/// Applied to a Church-encoded option it produces a Church-encoded boolean indicating whether it
/// is empty.
///
/// IS_NONE := λa.a TRUE (λx.FALSE) = λ 1 TRUE (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::church::option::is_none;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_none(), None.into_church()), NOR, 0), true.into_church());
/// assert_eq!(beta(app(is_none(), Some(1.into_church()).into_church()), NOR, 0), false.into_church());
/// ```
pub fn is_none() -> Term {
    abs(app!(Var(1), tru(), abs(fls())))
}

/// Applied to a Church-encoded option it produces a Church-encoded boolean indicating whether it
/// is not empty.
///
/// IS_SOME := λa.a FALSE (λx.TRUE) = λ 1 FALSE (λ TRUE)
///
/// # Example
/// ```
/// use lambda_calculus::church::option::is_some;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_some(), None.into_church()), NOR, 0), false.into_church());
/// assert_eq!(beta(app(is_some(), Some(2.into_church()).into_church()), NOR, 0), true.into_church());
/// ```
pub fn is_some() -> Term {
    abs(app!(Var(1), fls(), abs(tru())))
}

/// Applied to two arguments and a Church-encoded option it returns the second argument applied to
/// the option if it contains a value or the first argument if it doesn't.
///
/// MAP_OR := λdfm.m d f = λ λ λ 3 1 2
///
/// # Example
/// ```
/// use lambda_calculus::church::option::map_or;
/// use lambda_calculus::church::numerals::succ;
/// use lambda_calculus::*;
///
/// let some_one: Term = Some(1.into_church()).into_church();
///
/// assert_eq!(beta(app!(map_or(), 0.into_church(), succ(), some_one), NOR, 0), 2.into_church());
/// assert_eq!(beta(app!(map_or(), 0.into_church(), succ(), None.into_church()), NOR, 0), 0.into_church());
/// ```
pub fn map_or() -> Term {
    abs!(3, app!(Var(1), Var(3), Var(2)))
}

/// Applied to one argument and a Church-encoded option it returns the value inside the option or
/// the first argument if the option doesn't contain a value.
///
/// UNWRAP_OR := λdm.m d I = λ λ 1 2 I
///
/// # Example
/// ```
/// use lambda_calculus::church::option::unwrap_or;
/// use lambda_calculus::*;
///
/// let some_one: Term = Some(1.into_church()).into_church();
///
/// assert_eq!(beta(app!(unwrap_or(), 2.into_church(), some_one), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(unwrap_or(), 2.into_church(), None.into_church()), NOR, 0), 2.into_church());
/// ```
pub fn unwrap_or() -> Term {
    abs!(2, app!(Var(1), Var(2), abs(Var(1))))
}

impl IntoChurch for Option<Term> {
    fn into_church(self) -> Term {
        match self {
            None => none(),
            Some(value) => abs!(2, app(Var(1), value))
        }
    }
}
