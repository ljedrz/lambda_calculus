//! [Mogensen's binary number encoding](http://repository.readscheme.org/ftp/papers/topps/D-456.pdf)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls};
use crate::combinators::I;
use crate::data::pair::{pair, fst, snd};

/// A 0 bit; equivalent to `boolean::tru`.
///
/// B0 ≡ λab.a ≡ λ λ 2 ≡ TRUE
pub fn b0() -> Term { tru() }

/// A 1 bit; equivalent to `boolean::fls`.
///
/// B1 ≡ λab.b ≡ λ λ 1 ≡ FALSE
pub fn b1() -> Term { fls() }

/// Produces a binary-encoded number zero.
///
/// ZERO ≡ λzxy.z ≡ λ λ λ 3
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_binary());
/// ```
pub fn zero() -> Term { abs!(3, Var(3)) }

/// Applied to a binary-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO ≡ λn.n TRUE I (λx.FALSE) ≡ λ 1 TRUE I (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::is_zero;
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
/// ONE ≡ λzxy.y z ≡ λ λ λ 1 3
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_binary());
/// ```
pub fn one() -> Term {
    abs!(3, app(Var(1), Var(3)))
}

/// Applied to a binary-encoded number it produces its successor.
///
/// SUCC ≡ λn.SND (n Z A B) ≡ λ SND (1 Z A B)
///
/// where
///
/// Z ≡ PAIR ZERO ONE
///
/// A ≡ λp.p (λnm.PAIR (SHL0 n) (SHL1 n)) ≡ λ 1 (λ λ PAIR (SHL0 2) (SHL1 2))
///
/// B ≡ λp.p (λnm.PAIR (SHL1 n) (SHL0 m)) ≡ λ 1 (λ λ PAIR (SHL1 2) (SHL0 1))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_binary()), NOR, 0), 1.into_binary());
/// assert_eq!(beta(app(succ(), 1.into_binary()), NOR, 0), 2.into_binary());
/// assert_eq!(beta(app(succ(), 2.into_binary()), NOR, 0), 3.into_binary());
/// ```
pub fn succ() -> Term {
    let z = app!(pair(), zero(), one());
    let a = abs(app(Var(1), abs!(2, app!(pair(), app(shl0(), Var(2)), app(shl1(), Var(2))))));
    let b = abs(app(Var(1), abs!(2, app!(pair(), app(shl1(), Var(2)), app(shl0(), Var(1))))));

    abs(app(snd(), app!(Var(1), z, a, b)))
}

/// Applied to a binary-encoded number it produces its predecessor; inputs that are powers of number
/// 2 or return them may produce leading zeroes that can be removed using `strip`.
///
/// PRED ≡ λn.SND (n Z A B) ≡ λ SND (1 Z A B)
///
/// where
///
/// Z ≡ PAIR ZERO ZERO
///
/// A ≡ λp.p (λnm.PAIR (SHL0 n) (SHL1 m)) ≡ λ 1 (λ λ PAIR (SHL0 2) (SHL1 1))
///
/// B ≡ λp.p (λnm.PAIR (SHL1 n) (SHL0 n)) ≡ λ 1 (λ λ PAIR (SHL1 2) (SHL0 2))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::{pred, strip};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(strip(), app(pred(), 1.into_binary())), NOR, 0), 0.into_binary());
/// assert_eq!(beta(app(strip(), app(pred(), 2.into_binary())), NOR, 0), 1.into_binary());
/// assert_eq!(beta(app(pred(), 5.into_binary()), NOR, 0), 4.into_binary());
/// assert_eq!(beta(app(pred(), 6.into_binary()), NOR, 0), 5.into_binary());
/// ```
pub fn pred() -> Term {
    let z = app!(pair(), zero(), zero());
    let a = abs(app(Var(1), abs!(2, app!(pair(), app(shl0(), Var(2)), app(shl1(), Var(1))))));
    let b = abs(app(Var(1), abs!(2, app!(pair(), app(shl1(), Var(2)), app(shl0(), Var(2))))));

    abs(app(snd(), app!(Var(1), z, a, b)))
}

/// Applied to a binary-encoded number it returns its least significant bit.
///
/// LSB ≡ λn.n TRUE (λx.TRUE) (λx.FALSE) ≡ λ 1 TRUE (λ TRUE) (λ FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::{lsb, b0, b1};
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
/// SHL0 ≡ λnbzo.z (n b z o) ≡ λ λ λ λ 2 (4 3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::shl0;
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
/// SHL1 ≡ λnbzo.o (n b z o) ≡ λ λ λ λ 1 (4 3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::shl1;
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
/// STRIP ≡ λn.FST (n Z A B) ≡ λ FST (n Z A B)
///
/// where
///
/// Z ≡ PAIR ZERO TRUE
///
/// A ≡ λp.p (λnz.PAIR (z ZERO (SHL0 n)) z) ≡ λ 1 (λ λ PAIR (1 ZERO (SHL0 2)) 1)
///
/// B ≡ λp.p (λnz.PAIR (SHL1 n) FALSE) ≡ λ 1 (λ λ PAIR (SHL1 2) FALSE)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::binary::{strip, shl0};
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
    let z  = app!(pair(), zero(), tru());
    let a  = abs(app(Var(1), abs!(2, app!(pair(), app!(Var(1), zero(), app(shl0(), Var(2))), Var(1)))));
    let b  = abs(app(Var(1), abs!(2, app!(pair(), app(shl1(), Var(2)), fls()))));

    abs(app(fst(), app!(Var(1), z, a, b)))
}
