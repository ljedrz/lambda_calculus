//! [Signed numbers](https://en.wikipedia.org/wiki/Church_encoding#Signed_numbers)
//!
//! The supported `Encoding`s are `Church`, `Scott`, `Parigot` and `StumpFu`.

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::num::{church, scott, parigot, stumpfu};
use crate::data::num::convert::Encoding;
use crate::data::num::convert::Encoding::*;
use crate::data::pair::{fst, snd, pair, swap};
use crate::combinators::{I, Z};

/// Applied to a numeral with a specified encoding it produces a pair representing its signed
/// equivalent.
///
/// TO_SIGNED ≡ λx.PAIR x ZERO ≡ λ PAIR 1 ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::to_signed;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_signed(Church), 1.into_church()), NOR, 0), 1.into_signed(Church));
/// ```
pub fn to_signed(encoding: Encoding) -> Term {
    let zero = match encoding {
        Church  =>  church::zero(),
        Scott   =>   scott::zero(),
        Parigot => parigot::zero(),
        StumpFu => stumpfu::zero(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    abs(app!(pair(), Var(1), zero))
}

/// Applied to a signed integer it flips its sign.
///
/// NEG ≡ SWAP
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::neg;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(neg(), 1.into_signed(Church)), NOR, 0), (-1).into_signed(Church));
/// ```
pub fn neg() -> Term {
    swap()
}

/// Applied to a signed integer with a specified encoding, ensure that at least one element of the
/// pair representing it is equal to zero.
///
/// SIMPLIFY ≡ Z (λzx.IS_ZERO (FST x) (λy.x) (λy.IS_ZERO (SND x) x (z (PAIR (PRED (FST x))
/// (PRED (SND x))))) I) ≡
/// Z (λ λ IS_ZERO (FST 1) (λ 2) (λ IS_ZERO (SND 2) 2 (3 (PAIR (PRED (FST 2)) (PRED (SND 2))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::simplify;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(simplify(Church), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
/// assert_eq!(beta(app(simplify(Church), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
/// assert_eq!(beta(app(simplify(Church), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
/// ```
pub fn simplify(encoding: Encoding) -> Term {
    let is_zero = || match encoding {
        Church  =>  church::is_zero(),
        Scott   =>   scott::is_zero(),
        Parigot => parigot::is_zero(),
        StumpFu => stumpfu::is_zero(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    let pred = || match encoding {
        Church  =>  church::pred(),
        Scott   =>   scott::pred(),
        Parigot => parigot::pred(),
        StumpFu => stumpfu::pred(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    app(
        Z(),
        abs!(2, app!(
            is_zero(),
            app(fst(), Var(1)),
            abs(Var(2)),
            abs(app!(
                is_zero(),
                app(snd(), Var(2)),
                Var(2),
                app(
                    Var(3),
                    app!(
                        pair(),
                        app(pred(), app(fst(), Var(2))),
                        app(pred(), app(snd(), Var(2)))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to a signed integer with a specified encoding it returns its unsigned absolute value.
///
/// MODULUS ≡ λx.(λy.IS_ZERO (FST y) (SND y) (FST y)) (SIMPLIFY x) ≡
/// λ (λ IS_ZERO (FST 1) (SND 1) (FST 1)) (SIMPLIFY 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::modulus;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(modulus(Church),    1.into_signed(Church)), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(modulus(Church), (-1).into_signed(Church)), NOR, 0), 1.into_church());
/// ```
pub fn modulus(encoding: Encoding) -> Term {
    let is_zero = match encoding {
        Church  =>  church::is_zero(),
        Scott   =>   scott::is_zero(),
        Parigot => parigot::is_zero(),
        StumpFu => stumpfu::is_zero(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    abs(app(
        abs(app!(
            is_zero,
            app(fst(), Var(1)),
            app(snd(), Var(1)),
            app(fst(), Var(1))
        )),
        app(simplify(encoding), Var(1))
    ))
}

/// Applied to two signed integers with a specified encoding it returns a signed integer equal to
/// their sum.
///
/// ADD ≡ λab.SIMPLIFY (PAIR (ADD (FST a) (FST b)) (ADD (SND a) (SND b))) ≡
/// λ λ SIMPLIFY (PAIR (ADD (FST 2) (FST 1)) (ADD (SND 2) (SND 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::add;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(add(Church), (-1).into_signed(Church), 3.into_signed(Church)), NOR, 0),
///     beta(2.into_signed(Church), NOR, 0)
/// );
/// ```
pub fn add(encoding: Encoding) -> Term {
    let add = || match encoding {
        Church  =>  church::add(),
        Scott   =>   scott::add(),
        Parigot => parigot::add(),
        StumpFu => stumpfu::add(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    abs!(2, app(
        simplify(encoding),
        app!(
            pair(),
            app!(
                add(),
                app(fst(), Var(2)),
                app(fst(), Var(1))
            ),
            app!(
                add(),
                app(snd(), Var(2)),
                app(snd(), Var(1))
            )
        )
    ))
}

/// Applied to two signed integers with a specified encoding it returns a signed integer equal to
/// their difference.
///
/// SUB ≡ λab.SIMPLIFY (PAIR (ADD (FST a) (SND b)) (ADD (SND a) (FST b))) ≡
/// λ λ SIMPLIFY (PAIR (ADD (FST 2) (SND 1)) (ADD (SND 2) (FST 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::sub;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(sub(Church), 2.into_signed(Church), 3.into_signed(Church)), NOR, 0),
///     beta((-1).into_signed(Church), NOR, 0)
/// );
/// ```
pub fn sub(encoding: Encoding) -> Term {
    let add = || match encoding {
        Church  =>  church::add(),
        Scott   =>   scott::add(),
        Parigot => parigot::add(),
        StumpFu => stumpfu::add(),
        Binary  => panic!("signed binary numbers are not supported")
    };

    abs!(2, app(
        simplify(encoding),
        app!(
            pair(),
            app!(
                add(),
                app(fst(), Var(2)),
                app(snd(), Var(1))
            ),
            app!(
                add(),
                app(snd(), Var(2)),
                app(fst(), Var(1))
            )
        )
    ))
}

/// Applied to two signed integers with a specified encoding it returns a signed integer equal to
/// their product.
///
/// MUL ≡ λab.SIMPLIFY (PAIR (MUL (ADD (FST a) (FST b)) (ADD (SND a) (SND b)))
/// (MUL (ADD (FST a) (SND b)) (ADD (SND a) (FST b)))) ≡
/// λ λ SIMPLIFY (PAIR (MUL (ADD (FST 2) (FST 1)) (ADD (SND 2) (SND 1)))
/// (MUL (ADD (FST 2) (SND 1)) (ADD (SND 2) (FST 1))))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::mul;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(mul(Church), 2.into_signed(Church), (-3).into_signed(Church)), NOR, 0),
///     beta((-6).into_signed(Church), NOR, 0)
/// );
/// ```
pub fn mul(encoding: Encoding) -> Term {
    let mul = || match encoding {
        Church  => church::mul(),
        Scott   => scott::mul(),
        Parigot => parigot::mul(),
        StumpFu => stumpfu::mul(),
        Binary => panic!("signed binary numbers are not supported")
    };

    let add = || match encoding {
        Church => church::add(),
        Scott => scott::add(),
        Parigot => parigot::add(),
        StumpFu => stumpfu::add(),
        Binary => panic!("signed binary numbers are not supported")
    };

    abs!(2, app(
        simplify(encoding),
        app!(
            pair(),
            app!(
                add(),
                app!(
                    mul(),
                    app(fst(), Var(2)),
                    app(fst(), Var(1))
                ),
                app!(
                    mul(),
                    app(snd(), Var(2)),
                    app(snd(), Var(1))
                )
            ),
            app!(
                add(),
                app!(
                    mul(),
                    app(fst(), Var(2)),
                    app(snd(), Var(1))
                ),
                app!(
                    mul(),
                    app(snd(), Var(2)),
                    app(fst(), Var(1))
                )
            )
        )
    ))
}
