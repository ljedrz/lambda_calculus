//! [Lambda-encoded `n`-tuple](https://www.mathstat.dal.ca/~selinger/papers/lambdanotes.pdf)
//!
//! This module contains the `tuple` and `pi` macros.

/// A macro for creating lambda-encoded tuples.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::*;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     tuple!(1.into_church(), 2.into_church()),
///     abs(app!(Var(1), 1.into_church(), 2.into_church()))
/// );
///
/// assert_eq!(
///     tuple!(1.into_church(), 2.into_church(), 3.into_church()),
///     abs(app!(Var(1), 1.into_church(), 2.into_church(), 3.into_church()))
/// );
/// # }
/// ```
#[macro_export]
macro_rules! tuple {
    ($first:expr, $($next:expr),+) => {
        {
            let mut ret = app(Var(1), $first);
            $(ret = app(ret, $next);)*
            abs(ret)
        }
    };
}

/// A macro for obtaining a projection function (`π`) providing the `i`-th (one-indexed) element of
/// a lambda-encoded `n`-tuple.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::*;
/// use lambda_calculus::*;
///
/// let t2 = || tuple!(1.into_church(), 2.into_church());
///
/// assert_eq!(beta(app(pi!(1, 2), t2()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(pi!(2, 2), t2()), NOR, 0), 2.into_church());
///
/// let t3 = || tuple!(1.into_church(), 2.into_church(), 3.into_church());
///
/// assert_eq!(beta(app(pi!(1, 3), t3()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(pi!(2, 3), t3()), NOR, 0), 2.into_church());
/// assert_eq!(beta(app(pi!(3, 3), t3()), NOR, 0), 3.into_church());
/// # }
/// ```
#[macro_export]
macro_rules! pi {
    ($i:expr, $n:expr) => {
        {
            let mut ret = Var($n + 1 - $i);

            for _ in 0..$n {
                ret = abs(ret);
            }

            abs(app(Var(1), ret))
        }
    };
}
