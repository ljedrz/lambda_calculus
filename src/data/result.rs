//! Lambda-encoded [result type](https://doc.rust-lang.org/std/result/enum.Result.html)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls};
use crate::data::option::{none, some};
use crate::combinators::I;

/// Applied to an argument it consumes it and produces a lambda-encoded `Result::Ok` that contains
/// it.
///
/// OK ≡ λxab.a x ≡ λ λ λ 2 3
///
/// # Example
/// ```
/// use lambda_calculus::data::result::ok;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// assert_eq!(beta(app(ok(), 1.into_church()), NOR, 0), ok_one.into_church());
/// ```
pub fn ok() -> Term {
    abs!(3, app(Var(2), Var(3)))
}

/// Applied to an argument it consumes it and produces a lambda-encoded `Result::Err` that contains
/// it.
///
/// ERR ≡ λxab.b x ≡ λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::data::result::err;
/// use lambda_calculus::*;
///
/// let err_two: Result<usize, usize> = Err(2);
/// assert_eq!(beta(app(err(), 2.into_church()), NOR, 0), err_two.into_church());
/// ```
pub fn err() -> Term {
    abs!(3, app(Var(1), Var(3)))
}

/// Applied to a lambda-encoded `Result` it produces a lambda-encoded boolean indicating whether it
/// is `Result::Ok`.
///
/// IS_OK ≡ λa.a (λx.TRUE) (λx.FALSE) ≡ λ 1 (λ TRUE) (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::result::is_ok;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app(is_ok(), ok_one.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_ok(), err_two.into_church()), NOR, 0), false.into());
/// ```
pub fn is_ok() -> Term {
    abs(app!(Var(1), abs(tru()), abs(fls())))
}

/// Applied to a lambda-encoded `Result` it produces a lambda-encoded boolean indicating whether it
/// is `Result::Err`.
///
/// IS_ERR ≡ λa.a (λx.FALSE) (λx.TRUE) ≡ λ 1 (λ FALSE) (λ TRUE)
///
/// # Example
/// ```
/// use lambda_calculus::data::result::is_err;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app(is_err(), ok_one.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app(is_err(), err_two.into_church()), NOR, 0), true.into());
/// ```
pub fn is_err() -> Term {
    abs(app!(Var(1), abs(fls()), abs(tru())))
}

/// Applied to a lambda-encoded `Result` it produces a lambda-encoded `Option` containing the `Ok` value.
///
/// OPTION_OK ≡ λa.a SOME (λx.NONE) ≡ λ 1 SOME (λ NONE)
///
/// # Example
/// ```
/// use lambda_calculus::data::result::option_ok;
/// use lambda_calculus::data::option::none;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app(option_ok(), ok_one.into_church()), NOR, 0), Some(1).into_church());
/// assert_eq!(beta(app(option_ok(), err_two.into_church()), NOR, 0), none());
/// ```
pub fn option_ok() -> Term {
    abs(app!(Var(1), some(), abs(none())))
}

/// Applied to a lambda-encoded `Result` it produces a lambda-encoded `Option` containing the `Err`
/// value.
///
/// OPTION_ERR ≡ λa.a (λx.NONE) SOME ≡ λ 1 (λ NONE) SOME
///
/// # Example
/// ```
/// use lambda_calculus::data::result::option_err;
/// use lambda_calculus::data::option::none;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app(option_err(), ok_one.into_church()), NOR, 0), none());
/// assert_eq!(beta(app(option_err(), err_two.into_church()), NOR, 0), Some(2).into_church());
/// ```
pub fn option_err() -> Term {
    abs(app!(Var(1), abs(none()), some()))
}

/// Applied to a `Term` and a lambda-encoded `Result` it returns the value inside the `Ok` or
/// the first argument if the `Result` is not `Ok`.
///
/// UNWRAP_OR ≡ λdr.r I (λx.d) ≡ λ λ 1 I (λ 3)
///
/// # Example
/// ```
/// use lambda_calculus::data::result::unwrap_or;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app!(unwrap_or(), 3.into_church(), ok_one.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(unwrap_or(), 3.into_church(), err_two.into_church()), NOR, 0), 3.into_church());
/// ```
pub fn unwrap_or() -> Term {
    abs!(2, app!(Var(1), I(), abs(Var(3))))
}

/// Applied to a function and a lambda-encoded `Result` it applies the function to the contents of
/// the `Result` if it is `Ok`.
///
/// MAP ≡ λfm.m (λx.OK (f x)) ERR ≡ λ λ 1 (λ OK (3 1)) ERR
///
/// # Example
/// ```
/// use lambda_calculus::data::result::map;
/// use lambda_calculus::data::num::church::succ;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let ok_two: Result<usize, usize> = Ok(2);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(beta(app!(map(), succ(), ok_one.into_church()), NOR, 0), ok_two.into_church());
/// assert_eq!(beta(app!(map(), succ(), err_two.into_church()), NOR, 0), err_two.into_church());
/// ```
pub fn map() -> Term {
    abs!(2, app!(
        Var(1),
        abs(app(ok(), app(Var(3), Var(1)))),
        err()
    ))
}

/// Applied to a function and a lambda-encoded `Result` it applies the function to the contents of
/// the `Result` if it is `Err`.
///
/// MAP_ERR ≡ λfm.m OK (λx.ERR (f x)) ≡ λ λ 1 OK (λ ERR (3 1))
///
/// # Example
/// ```
/// use lambda_calculus::data::result::map_err;
/// use lambda_calculus::data::num::church::succ;
/// use lambda_calculus::*;
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let err_two: Result<usize, usize> = Err(2);
/// let err_three: Result<usize, usize> = Err(3);
///
/// assert_eq!(beta(app!(map_err(), succ(), ok_one.into_church()), NOR, 0), ok_one.into_church());
/// assert_eq!(beta(app!(map_err(), succ(), err_two.into_church()), NOR, 0), err_three.into_church());
/// ```
pub fn map_err() -> Term {
    abs!(2, app!(
        Var(1),
        ok(),
        abs(app(err(), app(Var(3), Var(1))))
    ))
}

/// Applied to a lambda-encoded `Result` and a function that returns a lambda-encoded `Result`, it
/// applies the function to the contents of the `Result` if it is `Ok`.
///
/// AND_THEN ≡ λmf.m f ERR ≡ λ λ 2 1 ERR
///
/// # Example
/// ```
/// use lambda_calculus::data::result::{and_then, ok};
/// use lambda_calculus::data::num::church::succ;
/// use lambda_calculus::*;
///
/// // Equivalent to a |x| { Ok(x + 1) } closure in Rust
/// let ok_succ: Term = abs(app(ok(), app(succ(), Var(1))));
///
/// let ok_one: Result<usize, usize> = Ok(1);
/// let ok_two: Result<usize, usize> = Ok(2);
/// let err_two: Result<usize, usize> = Err(2);
///
/// assert_eq!(
///     beta(app!(and_then(), err_two.into_church(), ok_succ.clone()), NOR, 0),
///     err_two.into_church()
/// );
///
/// assert_eq!(
///     beta(app!(and_then(), ok_one.into_church(), ok_succ.clone()), NOR, 0),
///     ok_two.into_church()
/// );
/// ```
pub fn and_then() -> Term {
    abs!(2, app!(Var(2), Var(1), err()))
}

impl Into<Term> for Result<Term, Term> {
    fn into(self) -> Term {
        match self {
            Ok(ok) => abs!(2, app(Var(2), ok)),
            Err(err) => abs!(2, app(Var(1), err))
        }
    }
}
