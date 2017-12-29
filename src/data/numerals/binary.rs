//! [Binary numbers](http://repository.readscheme.org/ftp/papers/topps/D-456.pdf)

use term::{Term, abs, app};
use term::Term::*;
use data::boolean::{tru, fls};
use combinators::I;

/// A 0 bit (equivalent to `booleans::tru`).
pub fn b0() -> Term { tru() }

/// A 1 bit (equivalent to `booleans::fls`).
pub fn b1() -> Term { fls() }

/// Produces a binary-encoded number zero.
///
/// ZERO := λzxy.z = λ λ λ 3
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_binary());
/// ```
pub fn zero() -> Term { abs!(3, Var(3)) }

/// Applied to a binary-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO := λn.n TRUE I (λx.FALSE) = λ 1 TRUE I (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::is_zero;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_zero(), 0.into_binary()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_zero(), 1.into_binary()), NOR, 0), false.into());
/// ```
pub fn is_zero() -> Term {
    abs(app!(Var(1), tru(), I(), abs(fls())))
}

/// Produces a binary-encoded number one.
///
/// ONE := λzxy.y z = λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_binary());
/// ```
pub fn one() -> Term {
    abs!(3, app(Var(1), Var(3)))
}
/*
/// Applied to a binary-encoded number it produces its successor.
///
/// SUCC := λn.π22 (n Z A B) = λ π22 (1 Z A B)
///
/// where
///
/// Z := (ZERO, ONE)
///
/// A := λp.p (λnm.(SHL0 n, SHL1 n)) = λ 1 (λ λ (SHL0 2, SHL1 2))
///
/// B := λp.p (λnm.(SHL1 n, SHL0 m)) = λ 1 (λ λ (SHL1 2, SHL0 1))
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_binary()), NOR, 0), 1.into_binary());
/// assert_eq!(beta(app(succ(), 1.into_binary()), NOR, 0), 2.into_binary());
/// assert_eq!(beta(app(succ(), 2.into_binary()), NOR, 0), 3.into_binary());
/// ```
pub fn succ() -> Term {
    let z  = tuple!(zero(), one());
    let a  = abs(app(Var(1), abs!(2, tuple!(app(shl0(), Var(2)), app(shl1(), Var(2))))));
    let b  = abs(app(Var(1), abs!(2, tuple!(app(shl1(), Var(2)), app(shl0(), Var(1))))));
    let pi = pi!(2, 2);

    abs(app(pi, app!(Var(1), z, a, b)))
}

/// Applied to a binary-encoded number it produces its predecessor.
///
/// PRED := λn.π22 (n Z A B) = λ π22 (1 Z A B)
///
/// where
///
/// Z := (ZERO, ZERO)
///
/// A := λp.p (λnm.(SHL0 n, SHL1 m)) = λ 1 (λ λ (SHL0 2, SHL1 1))
///
/// B := λp.p (λnm.(SHL1 n, SHL0 n)) = λ 1 (λ λ (SHL1 2, SHL0 2))
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into_binary()), NOR, 0), 0.into_binary());
/// assert_eq!(beta(app(pred(), 2.into_binary()), NOR, 0), 1.into_binary());
/// assert_eq!(beta(app(pred(), 3.into_binary()), NOR, 0), 2.into_binary());
/// ```
pub fn pred() -> Term {
    let z  = tuple!(zero(), zero());
    let a  = abs(app(Var(1), abs!(2, tuple!(app(shl0(), Var(2)), app(shl1(), Var(1))))));
    let b  = abs(app(Var(1), abs!(2, tuple!(app(shl1(), Var(2)), app(shl0(), Var(2))))));
    let pi = pi!(2, 2);

    abs(app(pi, app!(Var(1), z, a, b)))
}
*/
/// Applied to a binary-encoded number it returns its least significant bit.
///
/// LSB := λn.n TRUE (λx.TRUE) (λx.FALSE) = λ 1 TRUE (λ TRUE) (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::{lsb, b0, b1};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(lsb(), 1.into_binary()), NOR, 0), b1());
/// assert_eq!(beta(app(lsb(), 2.into_binary()), NOR, 0), b0());
/// assert_eq!(beta(app(lsb(), 3.into_binary()), NOR, 0), b1());
/// assert_eq!(beta(app(lsb(), 4.into_binary()), NOR, 0), b0());
/// ```
pub fn lsb() -> Term {
    abs(app!(Var(1), tru(), abs(tru()), abs(fls())))
}

/// Applied to a binary-encoded number it shifts it up by a single zero bit.
///
/// SHL0 := λnbzo.z (n b z o) = λ λ λ λ 2 (4 3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::shl0;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(shl0(), 1.into_binary()), NOR, 0), 2.into_binary());
/// assert_eq!(beta(app(shl0(), 2.into_binary()), NOR, 0), 4.into_binary());
/// assert_eq!(beta(app(shl0(), 3.into_binary()), NOR, 0), 6.into_binary());
/// ```
pub fn shl0() -> Term {
    abs!(4, app(Var(2), app!(Var(4), Var(3), Var(2), Var(1))))
}

/// Applied to a binary-encoded number it shifts it up by a single one bit.
///
/// SHL1 := λnbzo.o (n b z o) = λ λ λ λ 1 (4 3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::shl1;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(shl1(), 1.into_binary()), NOR, 0), 3.into_binary());
/// assert_eq!(beta(app(shl1(), 2.into_binary()), NOR, 0), 5.into_binary());
/// assert_eq!(beta(app(shl1(), 3.into_binary()), NOR, 0), 7.into_binary());
/// ```
pub fn shl1() -> Term {
    abs!(4, app(Var(1), app!(Var(4), Var(3), Var(2), Var(1))))
}

/// Applied to a binary-encoded number it strips its leading zeroes.
///
/// STRIP := λn.π12 (n Z A B) = λ π12 (n Z A B)
///
/// where
///
/// Z := (ZERO, TRUE)
///
/// A := λp.p (λnz.(z ZERO (SHL0 n), z)) = λ 1 (λ λ (1 ZERO (SHL0 2), 1))
///
/// B := λp.p (λnz.(SHL1 n, FALSE)) = λ 1 (λ λ (SHL1 2, FALSE))
///
/// # Example
/// ```
/// use lambda_calculus::data::numerals::binary::{strip, shl0};
/// use lambda_calculus::*;
///
/// let zero_with_a_leading_zero = beta(app(shl0(), 0.into_binary()), NOR, 0);
///
/// assert_eq!(
///     beta(app(strip(), zero_with_a_leading_zero), NOR, 0),
///     0.into_binary()
/// );
/// ```
pub fn strip() -> Term {
    let z  = tuple!(zero(), tru());
    let a  = abs(app(Var(1), abs!(2, tuple!(app!(Var(1), zero(), app(shl0(), Var(2))), Var(1)))));
    let b  = abs(app(Var(1), abs!(2, tuple!(app(shl1(), Var(2)), fls()))));
    let pi = pi!(1, 2);

    abs(app(pi, app!(Var(1), z, a, b)))
}
