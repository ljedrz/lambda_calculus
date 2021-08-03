//! [Lambda-encoded booleans](https://en.wikipedia.org/wiki/Church_encoding#Church_Booleans)

use crate::term::Term::*;
use crate::term::{abs, app, Term};

/// A lambda-encoded boolean `true`.
///
/// TRUE ≡ λab.a ≡ λ λ 2
pub fn tru() -> Term {
    abs!(2, Var(2))
}

/// A lambda-encoded boolean `false`.
///
/// FALSE ≡ λab.b ≡ λ λ 1
pub fn fls() -> Term {
    abs!(2, Var(1))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded conjunction.
///
/// AND ≡ λpq.p q p ≡ λ λ 2 1 2
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{and, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(and(), tru(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(and(), tru(), fls()), NOR, 0), fls());
/// assert_eq!(beta(app!(and(), fls(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(and(), fls(), fls()), NOR, 0), fls());
/// ```
pub fn and() -> Term {
    abs!(2, app!(Var(2), Var(1), Var(2)))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded disjunction.
///
/// OR ≡ λpq.p p q ≡ λ λ 2 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{or, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(or(), tru(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(or(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(or(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(or(), fls(), fls()), NOR, 0), fls());
/// ```
pub fn or() -> Term {
    abs!(2, app!(Var(2), Var(2), Var(1)))
}

/// Applied to a lambda-encoded boolean it returns its lambda-encoded negation.
///
/// NOT ≡ λp.p FALSE TRUE ≡ λ 1 FALSE TRUE
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{not, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(not(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(not(), fls()), NOR, 0), tru());
/// ```
pub fn not() -> Term {
    abs(app!(Var(1), fls(), tru()))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded exclusive disjunction.
///
/// XOR ≡ λpq.p (NOT q) q ≡ λ λ 2 (NOT 1) 1
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{xor, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(xor(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(xor(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(xor(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(xor(), fls(), fls()), NOR, 0), fls());
/// ```
pub fn xor() -> Term {
    abs!(2, app!(Var(2), app!(not(), Var(1)), Var(1)))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded joint denial.
///
/// NOR ≡ λpq.p p q FALSE TRUE ≡ λ λ 2 2 1 FALSE TRUE
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{nor, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(nor(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), tru(), fls()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), fls(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn nor() -> Term {
    abs!(2, app!(Var(2), Var(2), Var(1), fls(), tru()))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded exclusive joint denial
/// (`nor`); it is also known as `iff`.
///
/// XNOR ≡ λpq.p q (NOT q) ≡ λ λ 2 1 (NOT 1)
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{xnor, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(xnor(), tru(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(xnor(), tru(), fls()), NOR, 0), fls());
/// assert_eq!(beta(app!(xnor(), fls(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(xnor(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn xnor() -> Term {
    abs!(2, app!(Var(2), Var(1), app(not(), Var(1))))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded alternative denial.
///
/// NAND ≡ λpq.p q p FALSE TRUE ≡ λ λ 2 1 2 FALSE TRUE
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{nand, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(nand(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nand(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(nand(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(nand(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn nand() -> Term {
    abs!(2, app!(Var(2), Var(1), Var(2), fls(), tru()))
}

/// Applied to a lambda-encoded predicate and two terms it returns the first one if the predicate
/// is true or the second one if the predicate is false.
///
/// IF_ELSE ≡ λpab.p a b ≡ λ λ λ 3 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{if_else, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(if_else(), tru(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(if_else(), fls(), tru(), fls()), NOR, 0), fls());
/// ```
pub fn if_else() -> Term {
    abs!(3, app!(Var(3), Var(2), Var(1)))
}

/// Applied to two lambda-encoded booleans it returns their lambda-encoded implication.
///
/// IMPLY ≡ λpq.OR (NOT p) q ≡ λ λ OR (NOT 2) 1
///
/// # Examples
/// ```
/// use lambda_calculus::data::boolean::{imply, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(imply(), tru(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(imply(), tru(), fls()), NOR, 0), fls());
/// assert_eq!(beta(app!(imply(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(imply(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn imply() -> Term {
    abs!(2, app!(or(), app(not(), Var(2)), Var(1)))
}

impl From<bool> for Term {
    fn from(b: bool) -> Term {
        if b {
            tru()
        } else {
            fls()
        }
    }
}
