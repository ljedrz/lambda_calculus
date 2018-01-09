//! [Signed Church-encoded numerals](https://en.wikipedia.org/wiki/Church_encoding#Signed_numbers)

use term::{Term, abs, app};
use term::Term::*;
use data::num::church;
use data::pair::{fst, snd, pair, swap};
use combinators::{I, Z};

/// Applied to a Church-encoded numeral it produces a pair representing a signed Church-encoded
/// integer.
///
/// TO_SIGNED ≡ λx.PAIR x ZERO ≡ λ PAIR 1 ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::to_signed;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_signed(), 1.into_church()), NOR, 0), 1.into_signed());
/// ```
pub fn to_signed() -> Term {
    abs(app!(pair(), Var(1), church::zero()))
}

/// Applied to a pair representing a signed Church-encoded integer it flips the sign.
///
/// NEG ≡ SWAP
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::neg;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(neg(), 1.into_signed()), NOR, 0), (-1).into_signed());
/// ```
pub fn neg() -> Term {
    swap()
}

/// Applied to a pair of two Church-encoded numerals representing a signed integer, ensure that at
/// least one element of the pair is equal to 0.
///
/// SIMPLIFY ≡ Z (λz.λx.IS_ZERO (FST x) (λy.x) (λy.IS_ZERO (SND x) x (z (PAIR (PRED (FST x))
/// (PRED (SND x))))) I) ≡
/// Z (λ λ IS_ZERO (FST 1) (λ 2) (λ IS_ZERO (SND 2) 2 (3 (PAIR (PRED (FST 2)) (PRED (SND 2))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::simplify;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(simplify(), (3, 0).into_church()), NOR, 0), (3, 0).into_church());
/// assert_eq!(beta(app(simplify(), (0, 3).into_church()), NOR, 0), (0, 3).into_church());
/// assert_eq!(beta(app(simplify(), (4, 1).into_church()), NOR, 0), (3, 0).into_church());
/// ```
pub fn simplify() -> Term {
    app(
        Z(),
        abs!(2, app!(
            church::is_zero(),
            app(fst(), Var(1)),
            abs(Var(2)),
            abs(app!(
                church::is_zero(),
                app(snd(), Var(2)),
                Var(2),
                app(
                    Var(3),
                    app!(
                        pair(),
                        app(church::pred(), app(fst(), Var(2))),
                        app(church::pred(), app(snd(), Var(2)))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to a pair representing a signed Church-encoded integer it returns its absolute
/// value as a Church numeral.
///
/// MODULUS ≡ λx.(λy.IS_ZERO (FST y) (SND y) (FST y)) (NORMALIZE x) ≡
/// λ (λ IS_ZERO (FST 1) (SND 1) (FST 1)) (NORMALIZE 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::{to_signed, neg, modulus};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(modulus(), 1.into_signed()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(modulus(), (-1).into_signed()), NOR, 0), 1.into_church());
/// ```
pub fn modulus() -> Term {
    abs(app(
        abs(app!(
            church::is_zero(),
            app(fst(), Var(1)),
            app(snd(), Var(1)),
            app(fst(), Var(1))
        )),
        app(simplify(), Var(1))
    ))
}

/// Applied to a pair of two Church-encoded numerals representing a signed integer it returns a
/// pair representing their sum.
///
/// ADD ≡ λa.λb.NORMALIZE (PAIR (ADD (FST a) (FST b)) (ADD (SND a) (SND b))) ≡
/// λ λ NORMALIZE (PAIR (ADD (FST 2) (FST 1)) (ADD (SND 2) (SND 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::{to_signed, neg, add};
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(add(), (-1).into_signed(), 3.into_signed()), NOR, 0),
///     beta(2.into_signed(), NOR, 0)
/// );
/// ```
pub fn add() -> Term {
    abs!(2, app(
        simplify(),
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
/// pair representing their difference.
///
/// SUB ≡ λa.λb.NORMALIZE (PAIR (ADD (FST a) (SND b)) (ADD (SND a) (FST b))) ≡
/// λ λ NORMALIZE (PAIR (ADD (FST 2) (SND 1)) (ADD (SND 2) (FST 1)))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::signed::{to_signed, neg, sub};
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(sub(), 2.into_signed(), 3.into_signed()), NOR, 0),
///     beta((-1).into_signed(), NOR, 0)
/// );
/// ```
pub fn sub() -> Term {
    abs!(2, app(
        simplify(),
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
