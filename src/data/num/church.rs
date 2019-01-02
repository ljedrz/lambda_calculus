//! [Church numerals](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls, and, or, not};
use crate::data::num::{scott, parigot, stumpfu};
use crate::data::pair::pair;
use crate::combinators::{I, K, Z};

/// Produces a Church-encoded number zero; equivalent to `boolean::fls`.
///
/// ZERO ≡ λfx.x ≡ λ λ 1 ≡ FALSE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::zero;
/// use lambda_calculus::*;
///
/// assert_eq!(zero(), 0.into_church());
/// ```
pub fn zero() -> Term { fls() }

/// Applied to a Church-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO ≡ λn.n (λx.FALSE) TRUE ≡ λ 1 (λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::is_zero;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_zero(), 0.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_zero(), 1.into_church()), NOR, 0), false.into());
/// ```
pub fn is_zero() -> Term {
    abs(app!(Var(1), abs(fls()), tru()))
}

/// Produces a Church-encoded number one.
///
/// ONE ≡ λfx.f x ≡ λ λ 2 1
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::one;
/// use lambda_calculus::*;
///
/// assert_eq!(one(), 1.into_church());
/// ```
pub fn one() -> Term {
    abs!(2, app(Var(2), Var(1)))
}

/// Applied to a Church-encoded number it produces its successor.
///
/// SUCC ≡ λnfx.f (n f x) ≡ λ λ λ 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::succ;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(succ(), 0.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app(succ(), 1.into_church()), NOR, 0), 2.into_church());
/// ```
pub fn succ() -> Term {
    abs!(3, app(Var(2), app!(Var(3), Var(2), Var(1))))
}

/// Applied to a Church-encoded number it produces its predecessor.
///
/// PRED ≡ λnfx.n (λgh.h (g f)) (λu.x) (λu.u) ≡ λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::pred;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(pred(), 1.into_church()), NOR, 0), 0.into_church());
/// assert_eq!(beta(app(pred(), 3.into_church()), NOR, 0), 2.into_church());
/// ```
pub fn pred() -> Term {
    abs!(3, app!(
        Var(3),
        abs!(2, app(Var(1), app(Var(2), Var(4)))),
        abs(Var(2)),
        abs(Var(1))
    ))
}

/// Applied to two Church-encoded numbers it produces their sum.
///
/// ADD ≡ λmn.n SUCC m ≡ λ λ 1 SUCC 2
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::add;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(add(), 1.into_church(), 2.into_church()), NOR, 0), 3.into_church());
/// assert_eq!(beta(app!(add(), 2.into_church(), 3.into_church()), NOR, 0), 5.into_church());
/// ```
pub fn add() -> Term {
    abs!(2, app!(Var(1), succ(), Var(2)))
}

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// SUB ≡ λab.b PRED a ≡ λ λ 1 PRED 2
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::sub;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(sub(), 1.into_church(), 0.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(sub(), 3.into_church(), 1.into_church()), NOR, 0), 2.into_church());
/// assert_eq!(beta(app!(sub(), 5.into_church(), 2.into_church()), NOR, 0), 3.into_church());
/// ```
pub fn sub() -> Term {
    abs!(2, app!(Var(1), pred(), Var(2)))
}

/// Applied to two Church-encoded numbers it yields their product.
///
/// MUL ≡ λmnf.m (n f) ≡ λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::mul;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(mul(), 1.into_church(), 2.into_church()), NOR, 0), 2.into_church());
/// assert_eq!(beta(app!(mul(), 2.into_church(), 3.into_church()), NOR, 0), 6.into_church());
/// ```
pub fn mul() -> Term {
    abs!(3, app(Var(3), app(Var(2), Var(1))))
}

/// Applied to two Church-encoded numbers it raises the first one to the power of the second one.
///
/// POW ≡ λab.IS_ZERO b ONE (b a) ≡ λ λ IS_ZERO 1 ONE (1 2)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::pow;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(pow(), 3.into_church(), 0.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(pow(), 2.into_church(), 1.into_church()), NOR, 0), 2.into_church());
/// assert_eq!(beta(app!(pow(), 2.into_church(), 3.into_church()), NOR, 0), 8.into_church());
/// ```
pub fn pow() -> Term {
    abs!(2, app!(
        is_zero(),
        Var(1),
        one(),
        app(Var(1), Var(2))
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is less than the second one.
///
/// LT ≡ λab.NOT (LEQ b a) ≡ λ λ NOT (LEQ 1 2)
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::lt;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(lt(), 0.into_church(), 0.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(lt(), 1.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(lt(), 0.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(lt(), 1.into_church(), 0.into_church()), NOR, 0), false.into());
/// ```
pub fn lt() -> Term {
    abs!(2, app(
        not(),
        app!(
            leq(),
            Var(1),
            Var(2)
        )
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is less than or equal to the second one.
///
/// LEQ ≡ λmn.IS_ZERO (SUB m n) ≡ λ λ IS_ZERO (SUB 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::leq;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(leq(), 0.into_church(), 0.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(leq(), 1.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(leq(), 0.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(leq(), 1.into_church(), 0.into_church()), NOR, 0), false.into());
/// ```
pub fn leq() -> Term {
    abs!(2, app(
        is_zero(),
        app!(
            sub(),
            Var(2),
            Var(1)
        )
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is equal to the second one.
///
/// EQ ≡ λmn.AND (LEQ m n) (LEQ n m) ≡ λ λ AND (LEQ 2 1) (LEQ 1 2)
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::eq;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(eq(), 0.into_church(), 0.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(eq(), 1.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(eq(), 0.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(eq(), 1.into_church(), 0.into_church()), NOR, 0), false.into());
/// ```
pub fn eq() -> Term {
    abs!(2, app!(
        and(),
        app!(
            leq(),
            Var(2),
            Var(1)
        ),
        app!(
            leq(),
            Var(1),
            Var(2)
        )
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is not equal to the second one.
///
/// NEQ ≡ λab.OR (NOT (LEQ a b)) (NOT (LEQ b a)) ≡ λ λ OR (NOT (LEQ 2 1)) (NOT (LEQ 1 2))
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::neq;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(neq(), 0.into_church(), 0.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(neq(), 1.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(neq(), 0.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(neq(), 1.into_church(), 0.into_church()), NOR, 0), true.into());
/// ```
pub fn neq() -> Term {
    abs!(2, app!(
        or(),
        app(
            not(),
            app!(
                leq(),
                Var(2),
                Var(1)
            )
        ),
        app(
            not(),
            app!(
                leq(),
                Var(1),
                Var(2)
            )
        )
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is greater than or equal to the second one.
///
/// GEQ ≡ λab.LEQ b a ≡ λ λ LEQ 1 2
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::geq;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(geq(), 0.into_church(), 0.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(geq(), 1.into_church(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app!(geq(), 0.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(geq(), 1.into_church(), 0.into_church()), NOR, 0), true.into());
/// ```
pub fn geq() -> Term {
    abs!(2, app!(
        leq(),
        Var(1),
        Var(2)
    ))
}

/// Applied to two Church-encoded numbers it returns a lambda-encoded boolean indicating whether
/// its first argument is greater than the second one.
///
/// GT ≡ λab.NOT (LEQ a b) ≡ λ λ NOT (LEQ 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::data::num::church::gt;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(gt(), 0.into_church(), 0.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(gt(), 1.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(gt(), 0.into_church(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app!(gt(), 1.into_church(), 0.into_church()), NOR, 0), true.into());
/// ```
pub fn gt() -> Term {
    abs!(2, app(
        not(),
        app!(
            leq(),
            Var(2),
            Var(1)
        )
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded pair with the result of their
/// division - the quotient and the remainder.
///
/// DIV ≡ Z (λzqab.LT a b (λx.PAIR q a) (λx.z (SUCC q) (SUB a b) b) I) ZERO
///     ≡ Z (λ λ λ λ LT 2 1 (λ PAIR 4 3) (λ 5 (SUCC 4) (SUB 3 2) 2) I) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::div;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(div(), 4.into_church(), 2.into_church()), NOR, 0),
///     (2, 0).into_church()
/// );
/// assert_eq!(
///     beta(app!(div(), 5.into_church(), 3.into_church()), NOR, 0),
///     (1, 2).into_church()
/// );
/// ```
/// # Errors
///
/// This function will loop indefinitely if the divisor is `zero()`.
pub fn div() -> Term {
    app!(
        Z(),
        abs!(4, app!(
            lt(),
            Var(2),
            Var(1),
            abs(app!(
                pair(),
                Var(4),
                Var(3)
            )),
            abs(app!(
                Var(5),
                app(succ(), Var(4)),
                app!(sub(), Var(3), Var(2)),
                Var(2)
            )),
            I()
        )),
        zero()
    )
}

/// Applied to two Church-encoded numbers it returns a Church-encoded quotient of their division.
///
/// QUOT ≡ Z (λzab.LT a b (λx.ZERO) (λx.SUCC (z (SUB a b) b)) I)
///      ≡ Z (λ λ λ LT 2 1 (λ ZERO) (λ SUCC (4 (SUB 3 2) 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::quot;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(quot(), 4.into_church(), 2.into_church()), NOR, 0), 2.into_church());
/// assert_eq!(beta(app!(quot(), 5.into_church(), 3.into_church()), NOR, 0), 1.into_church());
/// ```
/// # Errors
///
/// This function will loop indefinitely if the second argument is `zero()`
pub fn quot() -> Term {
    app(
        Z(),
        abs!(3, app!(
            lt(),
            Var(2),
            Var(1),
            abs(zero()),
            abs(app(
                succ(),
                app!(
                    Var(4),
                    app!(sub(), Var(3), Var(2)),
                    Var(2)
                )
            )),
            I()
        ))
    )
}

/// Applied to two Church-encoded numbers it returns a Church-encoded remainder of their division.
///
/// REM ≡ Z (λzab.LT a b (λx.a) (λx.z (SUB a b) b) I) ≡ Z (λ λ λ LT 2 1 (λ 3) (λ 4 (SUB 3 2) 2) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::rem;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(rem(), 4.into_church(), 2.into_church()), NOR, 0), 0.into_church());
/// assert_eq!(beta(app!(rem(), 5.into_church(), 3.into_church()), NOR, 0), 2.into_church());
/// ```
/// # Errors
///
/// This function will loop indefinitely if the second argument is `zero()`
pub fn rem() -> Term {
    app(
        Z(),
        abs!(3, app!(
            lt(),
            Var(2),
            Var(1),
            abs(Var(3)),
            abs(app!(
                Var(4),
                app!(sub(), Var(3), Var(2)),
                Var(2)
            )),
            I()
        ))
     )
}

/// Applied to a Church-encoded number it yields its Church-encoded factorial.
///
/// FAC ≡ λn. n (λfab. f (MUL a b) (SUCC b)) K ONE ONE
///     ≡ λ 1 (λ λ λ 3 (MUL 2 1) (SUCC 1)) K ONE ONE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::fac;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(fac(), 3.into_church()), NOR, 0), 6.into_church());
/// assert_eq!(beta(app(fac(), 4.into_church()), NOR, 0), 24.into_church());
/// ```
/// # Errors
///
/// This function may overflow the stack if its argument is high enough.
pub fn fac() -> Term {
    abs(app!(
        Var(1),
        abs!(3, app!(
            Var(3),
            app!(mul(), Var(2), Var(1)),
            app!(succ(), Var(1))
        )),
        K(),
        one(),
        one()
    ))
}

/// Applied to two Church-encoded numbers it returns the smaller one.
///
/// MIN ≡ λaλb.(LEQ a b) a b ≡ λ λ (LEQ 2 1) 2 1
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::min;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(min(), 4.into_church(), 3.into_church()), NOR, 0), 3.into_church());
/// ```
pub fn min() -> Term {
	abs!(2, app!(
        app!(
            leq(),
            Var(2),
            Var(1)
        ),
        Var(2),
        Var(1)
    ))
}

/// Applied to two Church-encoded numbers it returns the greater one.
///
/// MAX ≡ λaλb.(LEQ a b) b a ≡ λ λ (LEQ 2 1) 1 2
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::max;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(max(), 4.into_church(), 3.into_church()), NOR, 0), 4.into_church());
/// ```
pub fn max() -> Term {
	abs!(2, app!(
        app!(
            leq(),
            Var(2),
            Var(1)
        ),
        Var(1),
        Var(2)
    ))
}

/// Applied to two Church-encoded numbers `a` and `b` it returns the left [logical
/// shift](https://en.wikipedia.org/wiki/Logical_shift) of `a` performed `b` times.
///
/// SHL ≡ λab.MUL a (POW (SUCC ONE) b) ≡ λ λ MUL 2 (POW (SUCC ONE) 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::shl;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(shl(), 0.into_church(), 2.into_church()), NOR, 0), 0.into_church());
/// assert_eq!(beta(app!(shl(), 1.into_church(), 0.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(shl(), 2.into_church(), 0.into_church()), NOR, 0), 2.into_church());
/// ```
pub fn shl() -> Term {
    abs!(2, app!(
        mul(),
        Var(2),
        app!(
            pow(),
            app(
                succ(),
                one()
            ),
            Var(1)
        )
    ))
}

/// Applied to two Church-encoded numbers `a` and `b` it returns the right [logical
/// shift](https://en.wikipedia.org/wiki/Logical_shift) of `a` performed `b` times.
///
/// SHR ≡ λab.IS_ZERO b a (QUOT a (POW (SUCC ONE) b))
///     ≡ λ λ IS_ZERO 1 2 (QUOT 2 (POW (SUCC ONE) 1))
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::shr;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app!(shr(), 0.into_church(), 2.into_church()), NOR, 0), 0.into_church());
/// assert_eq!(beta(app!(shr(), 2.into_church(), 1.into_church()), NOR, 0), 1.into_church());
/// assert_eq!(beta(app!(shr(), 2.into_church(), 0.into_church()), NOR, 0), 2.into_church());
/// ```
pub fn shr() -> Term {
    abs!(2, app!(
        is_zero(),
        Var(1),
        Var(2),
        app!(
            quot(),
            Var(2),
            app!(
                pow(),
                app(succ(), one()),
                Var(1)
            )
        )
    ))
}

/// Applied to a Church-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is even.
///
/// IS_EVEN ≡ λx.x NOT TRUE ≡ λ 1 NOT TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::is_even;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_even(), 0.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_even(), 1.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app(is_even(), 2.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_even(), 3.into_church()), NOR, 0), false.into());
/// ```
pub fn is_even() -> Term {
    abs(app!(Var(1), not(), tru()))
}

/// Applied to a Church-encoded number it produces a lambda-encoded boolean, indicating whether its
/// argument is odd.
///
/// IS_ODD ≡ λx.x NOT FALSE ≡ λ 1 NOT FALSE
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::is_odd;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_odd(), 0.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app(is_odd(), 1.into_church()), NOR, 0), true.into());
/// assert_eq!(beta(app(is_odd(), 2.into_church()), NOR, 0), false.into());
/// assert_eq!(beta(app(is_odd(), 3.into_church()), NOR, 0), true.into());
/// ```
pub fn is_odd() -> Term {
    abs(app!(Var(1), not(), fls()))
}

/// Applied to a Church-encoded number it produces the equivalent Scott-encoded number.
///
/// TO_SCOTT ≡ λn.n SUCC ZERO ≡ λ 1 SUCC ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::to_scott;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_scott(), 0.into_church()), NOR, 0), 0.into_scott());
/// assert_eq!(beta(app(to_scott(), 1.into_church()), NOR, 0), 1.into_scott());
/// assert_eq!(beta(app(to_scott(), 2.into_church()), NOR, 0), 2.into_scott());
/// ```
pub fn to_scott() -> Term {
    abs(app!(Var(1), scott::succ(), scott::zero()))
}

/// Applied to a Church-encoded number it produces the equivalent Parigot-encoded number.
///
/// TO_PARIGOT ≡ λn.n SUCC ZERO ≡ λ 1 SUCC ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::to_parigot;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_parigot(), 0.into_church()), NOR, 0), 0.into_parigot());
/// assert_eq!(beta(app(to_parigot(), 1.into_church()), NOR, 0), 1.into_parigot());
/// assert_eq!(beta(app(to_parigot(), 2.into_church()), NOR, 0), 2.into_parigot());
/// ```
pub fn to_parigot() -> Term {
    abs(app!(Var(1), parigot::succ(), parigot::zero()))
}

/// Applied to a Church-encoded number it produces the equivalent Stump-Fu-encoded number.
///
/// TO_STUMPFU ≡ λn.n SUCC ZERO ≡ λ 1 SUCC ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::num::church::to_stumpfu;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(to_stumpfu(), 0.into_church()), NOR, 0), 0.into_stumpfu());
/// assert_eq!(beta(app(to_stumpfu(), 1.into_church()), NOR, 0), 1.into_stumpfu());
/// assert_eq!(beta(app(to_stumpfu(), 2.into_church()), NOR, 0), 2.into_stumpfu());
/// ```
pub fn to_stumpfu() -> Term {
    abs(app!(Var(1), stumpfu::succ(), stumpfu::zero()))
}
