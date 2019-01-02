//! [Parigot list](https://ifl2014.github.io/submissions/ifl2014_submission_13.pdf)

use crate::term::{Term, abs, app, UD};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls};

/// Produces a `nil`, the last link of a Parigot-encoded list; equivalent to `boolean::tru`.
///
/// NIL ≡ λab.a ≡ λ λ 2 ≡ TRUE
pub fn nil() -> Term { tru() }

/// Applied to a Parigot-encoded list it determines if it is empty.
///
/// IS_NIL ≡ λl.l TRUE (λax.FALSE) ≡ λ 1 TRUE (λ λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::parigot::{is_nil, nil};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_nil(), nil()), NOR, 0), true.into());
/// ```
pub fn is_nil() -> Term {
    abs(app!(Var(1), tru(), abs!(2, fls())))
}

/// Applied to two terms it returns them contained in a Parigot-encoded list.
///
/// CONS ≡ λaxnc.c a x ((λl.l) x n c) ≡ λ λ λ λ 1 4 3 ((λ 1) 3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::parigot::{nil, cons};
/// use lambda_calculus::*;
///
/// let list_consed =
///     app!(
///         cons(),
///         1.into_parigot(),
///         app!(
///             cons(),
///             2.into_parigot(),
///             app!(
///                 cons(),
///                 3.into_parigot(),
///                 nil()
///             )
///         )
///     );
///
/// let list_into = vec![1, 2, 3].into_parigot();
///
/// assert_eq!(
///     beta(list_consed, NOR, 0),
///     list_into
/// );
/// ```
pub fn cons() -> Term {
    abs!(4, app!(
        Var(1),
        Var(4),
        Var(3),
        app!(
            abs(Var(1)),
            Var(3),
            Var(2),
            Var(1)
        )
    ))
}

/// Applied to a Parigot-encoded list it returns its first element.
///
/// HEAD ≡ λl.l UD (λhtx.h) ≡ λ 1 UD (λ λ λ 3)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::parigot::head;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_parigot();
///
/// assert_eq!(
///     beta(app(head(), list), NOR, 0),
///     1.into_parigot()
/// );
/// ```
pub fn head() -> Term {
    abs(app!(Var(1), UD, abs!(3, Var(3))))
}

/// Applied to a Parigot-encoded list it returns a new list with all its elements but the first one.
///
/// TAIL ≡ λl.l UD (λhtx.t) ≡ λ 1 UD (λ λ λ 2)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::parigot::tail;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_parigot();
///
/// assert_eq!(
///     beta(app(tail(), list), NOR, 0),
///     vec![2, 3].into_parigot()
/// );
/// ```
pub fn tail() -> Term {
    abs(app!(Var(1), UD, abs!(3, Var(2))))
}
