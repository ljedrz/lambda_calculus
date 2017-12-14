//! [Church booleans](https://en.wikipedia.org/wiki/Church_encoding#Church_Booleans)

use term::{Term, abs, app};
use term::Term::*;
use church::convert::IntoChurch;

/// A Church-encoded boolean `true`.
///
/// TRUE := λab.a = λ λ 2
pub fn tru() -> Term { abs!(2, Var(2)) }

/// A Church-encoded boolean `false`.
///
/// FALSE := λab.b = λ λ 1
pub fn fls() -> Term { abs!(2, Var(1)) }

/// Applied to two Church booleans it returns their Church-encoded conjunction.
///
/// AND := λpq.p q p = λ λ 2 1 2
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{and, tru, fls};
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

/// Applied to two Church booleans it returns their Church-encoded disjunction.
///
/// OR := λpq.p p q = λ λ 2 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{or, tru, fls};
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

/// Applied to a Church boolean it returns its Church-encoded negation.
///
/// NOT := λp.p FALSE TRUE = λ 1 FALSE TRUE
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{not, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(not(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(not(), fls()), NOR, 0), tru());
/// ```
pub fn not() -> Term {
    abs(app!(Var(1), fls(), tru()))
}

/// Applied to two Church booleans it returns their Church-encoded exclusive disjunction.
///
/// XOR := λpq.p (NOT q) q = λ λ 2 (NOT 1) 1
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{xor, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(xor(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(xor(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(xor(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(xor(), fls(), fls()), NOR, 0), fls());
/// ```
pub fn xor() -> Term {
    abs!(2,
        app!(
            Var(2),
            app!(
                Var(1),
                abs!(2, Var(1)),
                abs!(2, Var(2))
            ),
            Var(1)
        )
    )
}

/// Applied to two Church booleans it returns their Church-encoded joint denial.
///
/// NOR := λpq.NOT (OR p q) = λ λ NOT (OR 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{nor, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(nor(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), tru(), fls()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), fls(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nor(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn nor() -> Term {
    abs!(2,
        app!(
            Var(2),
            Var(2),
            Var(1),
            abs!(2, Var(1)),
            abs!(2, Var(2))
        )
    )
}

/// Applied to two Church booleans it returns their Church-encoded alternative denial.
///
/// NAND := λpq.NOT (AND p q) = λ λ NOT (AND 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{nand, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(nand(), tru(), tru()), NOR, 0), fls());
/// assert_eq!(beta(app!(nand(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(nand(), fls(), tru()), NOR, 0), tru());
/// assert_eq!(beta(app!(nand(), fls(), fls()), NOR, 0), tru());
/// ```
pub fn nand() -> Term {
    abs!(2,
        app!(
            Var(2),
            Var(1),
            Var(2),
            abs!(2, Var(1)),
            abs!(2, Var(2))
        )
    )
}

/// Applied to a Church-encoded predicate and two terms it returns the first one if the predicate
/// is true or the second one if the predicate is false.
///
/// IF_ELSE := λpab.p a b = λ λ λ 3 2 1
///
/// # Examples
/// ```
/// use lambda_calculus::church::boolean::{if_else, tru, fls};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(if_else(), tru(), tru(), fls()), NOR, 0), tru());
/// assert_eq!(beta(app!(if_else(), fls(), tru(), fls()), NOR, 0), fls());
/// ```
pub fn if_else() -> Term {
    abs!(3, app!(Var(3), Var(2), Var(1)))
}

impl IntoChurch for bool {
    fn into_church(self) -> Term {
        if self { tru() } else { fls() }
    }
}
