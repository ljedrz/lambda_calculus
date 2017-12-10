//! Church-encoded option type with methods based on `std::Option`

use term::{Term, abs, app};
use term::Term::*;
use church::booleans::{tru, fls};

/// Produces a Church-encoded Option containing nothing.
///
/// NONE := λns.n = λ λ 2
pub fn none() -> Term { tru() }

/// Applied to an argument it produces a Church-encoded Option containing the argument.
///
/// SOME := λans.s a = λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::church::option::some;
/// use lambda_calculus::*;
///
/// let some_one = app(some(), 1.into());
/// ```
pub fn some() -> Term {
    abs!(3, app(Var(1), Var(3)))
}

/// Applied to a Church-encoded Option it produces a Church-encoded boolean indicating whether its
/// argument is None.
///
/// IS_NONE := λa.a TRUE (λx.FALSE) = λ 1 TRUE (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::church::option::is_none;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_none(), None.into()), NOR, 0, false), true.into());
/// assert_eq!(beta(app(is_none(), Some(1.into()).into()), NOR, 0, false), false.into());
/// ```
pub fn is_none() -> Term {
    abs(app!(Var(1), tru(), abs(fls())))
}

/// Applied to a Church-encoded Option it produces a Church-encoded boolean indicating whether its
/// argument is Some.
///
/// IS_SOME := λa.a FALSE (λx.TRUE) = λ 1 FALSE (λ TRUE)
///
/// # Example
/// ```
/// use lambda_calculus::church::option::is_some;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_some(), None.into()), NOR, 0, false), false.into());
/// assert_eq!(beta(app(is_some(), Some(2.into()).into()), NOR, 0, false), true.into());
/// ```
pub fn is_some() -> Term {
    abs(app!(Var(1), fls(), abs(tru())))
}

/// Applied to two arguments and a Church-encoded option, return second argument applied to the
/// Church-encoded option if the option contains a value; otherwise, return the first argument.
///
/// MAP_OR := λdfm.m d f = λ λ λ 3 1 2
///
/// # Example
/// ```
/// use lambda_calculus::church::option::map_or;
/// use lambda_calculus::church::numerals::succ;
/// use lambda_calculus::*;
///
/// let some_one: Term = Some(1.into()).into();
///
/// assert_eq!(beta(app!(map_or(), 0.into(), succ(), some_one.clone()), NOR, 0, false), 2.into());
/// ```
pub fn map_or() -> Term {
    abs!(3, app!(Var(1), Var(3), Var(2)))
}

impl From<Option<Term>> for Term {
    fn from(option: Option<Term>) -> Self {
        match option {
            None => none(),
            Some(value) => abs!(2, app(Var(1), value))
        }
    }
}
