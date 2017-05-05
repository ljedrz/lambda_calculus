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
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::booleans::{and, tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(and(), tru(), tru())), tru());
/// assert_eq!(beta_full(app!(and(), tru(), fls())), fls());
/// assert_eq!(beta_full(app!(and(), fls(), tru())), fls());
/// assert_eq!(beta_full(app!(and(), fls(), fls())), fls());
/// # }
/// ```
pub fn and() -> Term {
    abs(abs(
        app!(Var(2), Var(1), Var(2))
    ))
}

/// Applied to two Church-encoded booleans it returns their Church-encoded disjunction.
///
/// OR := λpq.p p q = λ λ 2 2 1
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::booleans::{or, tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(or(), tru(), tru())), tru());
/// assert_eq!(beta_full(app!(or(), tru(), fls())), tru());
/// assert_eq!(beta_full(app!(or(), fls(), tru())), tru());
/// assert_eq!(beta_full(app!(or(), fls(), fls())), fls());
/// # }
/// ```
pub fn or() -> Term {
    abs(abs(
        app!(Var(2), Var(2), Var(1))
    ))
}

/// Applied to a Church-encoded boolean it returns its Church-encoded negation.
///
/// NOT := λp.p FALSE TRUE = λ 1 FALSE TRUE
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::booleans::{not, tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(not(), tru())), fls());
/// assert_eq!(beta_full(app!(not(), fls())), tru());
/// # }
/// ```
pub fn not() -> Term {
    abs(
        app!(Var(1), fls(), tru())
    )
}

/// Applied to a Church-encoded boolean it returns its Church-encoded exclusive disjunction.
///
/// XOR := λab.a (NOT b) b = λ λ 2 (NOT 1) 1
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::booleans::{xor, tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(xor(), tru(), tru())), fls());
/// assert_eq!(beta_full(app!(xor(), tru(), fls())), tru());
/// assert_eq!(beta_full(app!(xor(), fls(), tru())), tru());
/// assert_eq!(beta_full(app!(xor(), fls(), fls())), fls());
/// # }
/// ```
pub fn xor() -> Term {
    abs(abs(
        app!(Var(2), app!(not(), Var(1)), Var(1))
    ))
}

/// Applied to a Church encoded predicate and two terms it returns the first one if the predicate
/// is true or the second one if the predicate is false.
///
/// IF_ELSE := λpab.p a b = λ λ λ 3 2 1
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::booleans::{if_else, tru, fls};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(app!(if_else(), tru(), one(), zero())), one());
/// assert_eq!(beta_full(app!(if_else(), fls(), one(), zero())), zero());
/// # }
/// ```
pub fn if_else() -> Term {
    abs(abs(abs(
        app!(Var(3), Var(2), Var(1))
    )))
}

impl From<bool> for Term {
    fn from(b: bool) -> Self {
        if b { tru() } else { fls() }
    }
}
