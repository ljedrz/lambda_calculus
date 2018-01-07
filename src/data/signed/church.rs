//! Signed Church-encoded numerals

use term::{Term, abs, app};
use term::Term::*;
use data::num::church;
use data::pair::{fst, snd, pair, swap};
use combinators::Z;

/// Applied to a Church-encoded numeral it produces a pair representing a signed Church-encoded
/// integer.
///
/// TO_SIGNED ≡ λx.PAIR x ZERO ≡ λ PAIR 1 ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::to_signed;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_signed(), 1.into_church()), NOR, 0), (1, 0).into_church());
/// ```
pub fn to_signed() -> Term {
    abs(app!(pair(), Var(1), church::zero()))
}

/// Applied to a pair representing a signed Church-encoded integer it flips the sign.
///
/// NEGATE ≡ SWAP
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::negate;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(negate(), (1, 0).into_church()), NOR, 0), (0, 1).into_church());
/// ```
pub fn negate() -> Term {
    swap()
}

/// Applied to a pair of two Church-encoded numerals representing a signed integer, ensure that at
/// least one element of the pair is equal to 0.
///
/// NORMALIZE ≡ Z (λz.λx.IS_ZERO (FST x) (λy.x) (λy.IS_ZERO (SND x) x (z (PAIR (PRED (FST x))
/// (PRED (SND x))))) I) ≡
/// Z (λ λ IS_ZERO (FST 1) (λ 2) (λ IS_ZERO (SND 2) 2 (3 (PAIR (PRED (FST 2)) (PRED (SND 2))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::normalize;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(normalize(), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
/// assert_eq!(beta(app(normalize(), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
/// assert_eq!(beta(app(normalize(), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
/// ```
pub fn normalize() -> Term {
    app(
        Z(),
        abs!(2, app!(
            Var(1),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs!(2, Var(2)),
            abs(Var(2)),
            abs(app!(
                Var(2),
                abs!(2, Var(1)),
                abs!(3, Var(1)),
                abs!(2, Var(2)),
                Var(2),
                app!(
                    Var(3),
                    abs(app!(
                        Var(1),
                        abs!(2, app!(
                            Var(5),
                            abs!(2, Var(2)),
                            abs!(2, app!(
                                Var(1),
                                app(Var(2), Var(4))
                            )),
                            abs(Var(2)),
                            abs(Var(1))
                        )),
                        abs!(2, app!(
                            Var(5),
                            abs!(2, Var(1)),
                            abs!(2, app!(
                                Var(1),
                                app(Var(2), Var(4))
                            )),
                            abs(Var(2)),
                            abs(Var(1))
                        ))
                    ))
                )
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a pair representing a signed Church-encoded integer it returns its absolute
/// value as a Church numeral.
///
/// ABSOLUTE_VALUE ≡ λx.(λy.IS_ZERO (FST y) (SND y) (FST y)) (NORMALIZE x) ≡
/// λ (λ IS_ZERO (FST 1) (SND 1) (FST 1)) (NORMALIZE 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::{to_signed, negate, absolute_value};
/// use lambda_calculus::*;
///
/// let one = app(to_signed(), 1.into_church());
/// let neg_one = app(negate(), one.clone());
///
/// assert_eq!(beta(app(absolute_value(), one.clone()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(absolute_value(), neg_one.clone()), NOR, 0), 1.into_church());
/// ```
pub fn absolute_value() -> Term {
    abs(app(
        abs(app!(
            church::is_zero(),
            app(fst(), Var(1)),
            app(snd(), Var(1)),
            app(fst(), Var(1))
        )),
        app(normalize(), Var(1))
    ))
}

/// Applied to a pair of two Church-encoded numerals representing a signed integer it returns a
/// normalized pair representing their sum.
///
/// SIGNED_ADD ≡ λa.λb.NORMALIZE (PAIR (ADD (FST a) (FST b)) (ADD (SND a) (SND b))) ≡
/// λ λ NORMALIZE (PAIR (ADD (FST 2) (FST 1)) (ADD (SND 2) (SND 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::{to_signed, negate, signed_add};
/// use lambda_calculus::*;
///
/// let two = app(to_signed(), 2.into_church());
/// let three = app(to_signed(), 3.into_church());
/// let neg_one = app(negate(), app(to_signed(), 1.into_church()));
///
/// assert_eq!(
///     beta(app!(signed_add(), neg_one.clone(), three.clone()), NOR, 0),
///     beta(two.clone(), NOR, 0)
/// );
/// ```
pub fn signed_add() -> Term {
    abs!(2, app(
        normalize(),
        app!(
            pair(),
            app!(
                church::add(),
                app(fst(), Var(2)),
                app(fst(), Var(1))
            ),
            app!(
                church::add(),
                app(snd(), Var(2)),
                app(snd(), Var(1))
            )
        )
    ))
}

/// Applied to a pair of two Church-encoded numerals representing a signed integer it returns a
/// normalized pair representing their difference.
///
/// SIGNED_SUB ≡ λa.λb.NORMALIZE (PAIR (ADD (FST a) (SND b)) (ADD (SND a) (FST b))) ≡
/// λ λ NORMALIZE (PAIR (ADD (FST 2) (SND 1)) (ADD (SND 2) (FST 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::signed::church::{to_signed, negate, signed_sub};
/// use lambda_calculus::*;
///
/// let two = app(to_signed(), 2.into_church());
/// let three = app(to_signed(), 3.into_church());
/// let neg_one = app(negate(), app(to_signed(), 1.into_church()));
///
/// assert_eq!(
///     beta(app!(signed_sub(), two.clone(), three.clone()), NOR, 0),
///     beta(neg_one.clone(), NOR, 0)
/// );
/// ```
pub fn signed_sub() -> Term {
    abs!(2, app(
        normalize(),
        app!(
            pair(),
            app!(
                church::add(),
                app(fst(), Var(2)),
                app(snd(), Var(1))
            ),
            app!(
                church::add(),
                app(snd(), Var(2)),
                app(fst(), Var(1))
            )
        )
    ))
}
