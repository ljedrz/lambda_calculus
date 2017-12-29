//! [Lambda-encoded `n`-tuple](https://www.mathstat.dal.ca/~selinger/papers/lambdanotes.pdf)
//!
//! This module contains the `tuple` and `projection` macros.

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
/// let t    = tuple!(1.into_church(), 2.into_church(), 3.into_church());
/// let pi23 = pi!(2, 3);
///
/// assert_eq!(beta(app(pi23, t), NOR, 0), 2.into_church());
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
