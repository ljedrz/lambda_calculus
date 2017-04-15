//! [Church booleans](https://en.wikipedia.org/wiki/Church_encoding#Church_Booleans)

use term::*;
use term::Term::*;

/// A Church-encoded boolean `true`.
///
/// TRUE := λab.a = λ λ 2
pub fn tru() -> Term { abs(abs(Var(2))) }

/// A Church-encoded boolean `false`.
///
/// FALSE := λab.b = λ λ 1
pub fn fls() -> Term { abs(abs(Var(1))) }

/// Applied to two Church-encoded booleans it returns their Church-encoded conjunction.
///
/// AND := λpq.p q p = λ λ 2 1 2
///
/// # Examples
/// ```
/// use lambda_calculus::booleans::{and, tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(and().app(tru()).app(tru())), tru());
/// assert_eq!(normalize(and().app(tru()).app(fls())), fls());
/// assert_eq!(normalize(and().app(fls()).app(tru())), fls());
/// assert_eq!(normalize(and().app(fls()).app(fls())), fls());
/// ```
pub fn and() -> Term {
    abs(abs(
        Var(2)
        .app(Var(1))
        .app(Var(2))
    ))
}

/// Applied to two Church-encoded booleans it returns their Church-encoded disjunction.
///
/// OR := λpq.p p q = λ λ 2 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::booleans::{or, tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(or().app(tru()).app(tru())), tru());
/// assert_eq!(normalize(or().app(tru()).app(fls())), tru());
/// assert_eq!(normalize(or().app(fls()).app(tru())), tru());
/// assert_eq!(normalize(or().app(fls()).app(fls())), fls());
/// ```
pub fn or() -> Term {
    abs(abs(
        Var(2)
        .app(Var(2))
        .app(Var(1))
    ))
}

/// Applied to a Church-encoded boolean it returns its Church-encoded negation.
///
/// NOT := λp.p FALSE TRUE = λ 1 FALSE TRUE
///
/// # Examples
/// ```
/// use lambda_calculus::booleans::{not, tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(not().app(tru())), fls());
/// assert_eq!(normalize(not().app(fls())), tru());
/// ```
pub fn not() -> Term {
    abs(
        Var(1)
        .app(fls())
        .app(tru())
    )
}

/// Applied to a Church-encoded boolean it returns its Church-encoded exclusive disjunction.
///
/// XOR := λab.a (NOT b) b = λ λ 2 (NOT 1) 1
///
/// # Examples
/// ```
/// use lambda_calculus::booleans::{xor, tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(xor().app(tru()).app(tru())), fls());
/// assert_eq!(normalize(xor().app(tru()).app(fls())), tru());
/// assert_eq!(normalize(xor().app(fls()).app(tru())), tru());
/// assert_eq!(normalize(xor().app(fls()).app(fls())), fls());
/// ```
pub fn xor() -> Term {
    abs(abs(
        Var(2)
        .app(not().app(Var(1)))
        .app(Var(1))
    ))
}

/// Applied to a Church encoded predicate and two terms it returns the first one if the predicate
/// is true or the second one if the predicate is false.
///
/// IF_ELSE := λpab.p a b = λ λ λ 3 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::booleans::{if_else, tru, fls};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(if_else().app(tru()).app(one()).app(zero())), one());
/// assert_eq!(normalize(if_else().app(fls()).app(one()).app(zero())), zero());
/// ```
pub fn if_else() -> Term {
    abs(abs(abs(
        Var(3)
        .app(Var(2))
        .app(Var(1))
    )))
}
