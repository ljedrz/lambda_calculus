//! [Church numerals](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals)

use term::{Term, Error, abs, app};
use term::Term::*;
use term::Error::*;
use church::booleans::{tru, fls};
use combinators::z;

/// Produces a Church-encoded number zero.
///
/// ZERO := λfx.x = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::church::numerals::zero;
/// use lambda_calculus::term::Term;
///
/// assert_eq!(zero(), Term::from(0));
/// ```
pub fn zero() -> Term { abs(abs(Var(1))) }

/// Applied to a Church-encoded number it produces a Church-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO := λn.n (λx.FALSE) TRUE =  λ 1 (λ FALSE) TRUE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::is_zero;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(is_zero(), 0.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(is_zero(), 1.into()), NOR, 0, false), fls());
/// # }
/// ```
pub fn is_zero() -> Term {
    abs(
        app!(Var(1), abs(fls()), tru())
    )
}

/// Produces a Church-encoded number one.
///
/// ONE := λfx.f x = λ λ 2 1
///
/// # Example
/// ```
/// use lambda_calculus::church::numerals::one;
/// use lambda_calculus::term::Term;
///
/// assert_eq!(one(), Term::from(1));
/// ```
pub fn one() -> Term {
    abs(abs(
        app(Var(2), Var(1))
    ))
}

/// Applied to a Church-encoded number it produces its successor.
///
/// SUCC := λnfx.f (n f x) = λ λ λ 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::church::numerals::succ;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = succ().app(0.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 1.into());
/// ```
pub fn succ() -> Term {
    abs(abs(abs(
        app(Var(2), app!(Var(3), Var(2), Var(1)))
    )))
}

/// Applied to two Church-encoded numbers it produces their sum.
///
/// PLUS := λmnfx.m f (n f x) = λ λ λ λ 4 2 (3 2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(plus(), 3.into(), 2.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 5.into());
/// # }
/// ```
pub fn plus() -> Term {
    abs(abs(abs(abs(
        app!(Var(4), Var(2), app!(Var(3), Var(2), Var(1)))
    ))))
}

/// Applied to two Church-encoded numbers it yields their product.
///
/// MULT := λmnf.m (n f) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::mult;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(mult(), 2.into(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 6.into());
/// # }
/// ```
pub fn mult() -> Term {
    abs(abs(abs(
        app(Var(3), app(Var(2), Var(1)))
    )))
}

/// Applied to two Church-encoded numbers it raises the first one to the power of the second one.
///
/// POW := λab.IS_ZERO b ONE (b a) = λ λ IS_ZERO 1 ONE (1 2)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::pow;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(pow(), 2.into(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 8.into());
/// # }
/// ```
pub fn pow() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        one(),
        app(Var(1), Var(2))
    )))
}

/// Applied to a Church-encoded number it produces its predecessor.
///
/// PRED := λnfx.n (λgh.h (g f)) (λu.x) (λu.u) = λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::church::numerals::pred;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = pred().app(3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 2.into());
/// ```
pub fn pred() -> Term {
    abs(abs(abs(app!(
        Var(3),
        abs(abs(app(Var(1), app(Var(2), Var(4))))),
        abs(Var(2)),
        abs(Var(1))
    ))))
}

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// SUB := λab.b PRED a = λ λ 1 PRED 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::sub;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(sub(), 5.into(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 2.into());
/// # }
/// ```
pub fn sub() -> Term {
    abs(abs(
        app!(Var(1), pred(), Var(2))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is less than the second one.
///
/// LT := λab.NOT (LEQ b a) = λ λ NOT (LEQ 1 2)
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::lt;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(lt(), 0.into(), 0.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(lt(), 1.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(lt(), 0.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(lt(), 1.into(), 0.into()), NOR, 0, false), fls());
/// # }
/// ```
pub fn lt() -> Term {
    abs(abs(app!(
        Var(2),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(1),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        abs(abs(Var(1))),
        abs(abs(Var(2)))
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is less than or egual to the second one.
///
/// LEQ := λmn.IS_ZERO (SUB m n) = λ λ IS_ZERO (SUB 2 1)
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::leq;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(leq(), 0.into(), 0.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(leq(), 1.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(leq(), 0.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(leq(), 1.into(), 0.into()), NOR, 0, false), fls());
/// # }
/// ```
pub fn leq() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2)))
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is egual to the second one.
///
/// EQ := λmn.AND (LEQ m n) (LEQ n m) = λ λ AND (LEQ 2 1) (LEQ 1 2)
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::eq;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(eq(), 0.into(), 0.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(eq(), 1.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(eq(), 0.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(eq(), 1.into(), 0.into()), NOR, 0, false), fls());
/// assert_eq!(beta(eq(), NOR, 0, false), eq());
/// # }
/// ```
pub fn eq() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        app!(
            Var(2),
            abs(abs(abs(
                app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
            ))),
            Var(1),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2)))
        ),
        app!(
            Var(1),
            abs(abs(abs(
                app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
            ))),
            Var(2),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2)))
        )
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is not egual to the second one.
///
/// NEQ := λab.OR (NOT (LEQ a b)) (NOT (LEQ b a)) = λ λ OR (NOT (LEQ 2 1)) (NOT (LEQ 1 2))
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::neq;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(neq(), 0.into(), 0.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(neq(), 1.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(neq(), 0.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(neq(), 1.into(), 0.into()), NOR, 0, false), tru());
/// # }
/// ```
pub fn neq() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        abs(abs(Var(1))),
        abs(abs(Var(2))),
        app!(
            Var(1),
            abs(abs(abs(
                app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
            ))),
            Var(2),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(Var(1))),
            abs(abs(Var(2)))
        ),
        app!(
            Var(2),
            abs(abs(abs(
                app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
            ))),
            Var(1),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(Var(1))),
            abs(abs(Var(2)))
        )
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is greater than or egual to the second one.
///
/// GEQ := λab.LEQ b a = λ λ LEQ 1 2
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::geq;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(geq(), 0.into(), 0.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(geq(), 1.into(), 1.into()), NOR, 0, false), tru());
/// assert_eq!(beta(app!(geq(), 0.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(geq(), 1.into(), 0.into()), NOR, 0, false), tru());
/// # }
/// ```
pub fn geq() -> Term {
    abs(abs(app!(
        Var(2),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(1),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2)))
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is greater than the second one.
///
/// GT := λab.NOT (LEQ a b) = λ λ NOT (LEQ 2 1)
///
/// # Examples
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::gt;
/// use lambda_calculus::church::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(gt(), 0.into(), 0.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(gt(), 1.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(gt(), 0.into(), 1.into()), NOR, 0, false), fls());
/// assert_eq!(beta(app!(gt(), 1.into(), 0.into()), NOR, 0, false), tru());
/// # }
/// ```
pub fn gt() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        abs(abs(Var(1))),
        abs(abs(Var(2)))
    )))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded pair with the result of their
/// division - the quotient and the remainder. It loops indefinitely if the divisor is `zero()`.
///
/// DIV := Z (λzqab.LT a b (λx.PAIR q a) (λx.z (SUCC q) (SUB a b) b) I) ZERO =
/// Z (λ λ λ λ LT 2 1 (λ PAIR 4 3) (λ 5 (SUCC 4) (SUB 3 2) 2) I) ZERO
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::div;
/// use lambda_calculus::term::Term;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(div(), 5.into(), 2.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, Term::from((2.into(), 1.into())));
/// # }
/// ```
pub fn div() -> Term {
    app!(
        z(),
        abs(abs(abs(abs(app!(
            Var(2),
            abs(abs(abs(app!(
                Var(3),
                abs(abs(app(Var(1), app(Var(2), Var(4))))),
                abs(Var(2)),
                abs(Var(1))
            )))),
            Var(1),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(Var(1))),
            abs(abs(Var(2))),
            abs(abs(app!(Var(1), Var(5), Var(4)))),
            abs(app!(
                Var(5),
                abs(abs(app(
                    Var(2),
                    app!(Var(6), Var(2), Var(1))
                ))),
                app!(
                    Var(2),
                    abs(abs(abs(app!(
                        Var(3),
                        abs(abs(app(Var(1), app(Var(2), Var(4))))),
                        abs(Var(2)),
                        abs(Var(1))
                    )))),
                    Var(3)
                ),
                Var(2)
            )),
            abs(Var(1))
        ))))),
        zero()
    )
}

/// Applied to two Church-encoded numbers it returns a Church-encoded quotient of their division.
/// It loops indefinitely if the second argument is `zero()`.
///
/// QUOT := Z (λzab.LT a b (λx.ZERO) (λx.SUCC (z (SUB a b) b)) I) =
/// Z (λ λ λ LT 2 1 (λ ZERO) (λ SUCC (4 (SUB 3 2) 2)) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::quot;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(quot(), 6.into(), 2.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 3.into());
/// # }
/// ```
pub fn quot() -> Term {
    app(
        z(),
        abs(abs(abs(app!(
            Var(2),
            abs(abs(abs(app!(
                Var(3),
                abs(abs(app(Var(1), app(Var(2), Var(4))))),
                abs(Var(2)),
                abs(Var(1))
            )))),
            Var(1),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(Var(1))),
            abs(abs(Var(2))),
            abs(abs(abs(Var(1)))),
            abs(abs(abs(app(
                Var(2),
                app!(
                    Var(6),
                    app!(
                        Var(4),
                        abs(abs(abs(app!(
                            Var(3),
                            abs(abs(app(Var(1), app(Var(2), Var(4))))),
                            abs(Var(2)),
                            abs(Var(1))
                        )))),
                        Var(5)
                    ),
                    Var(4),
                    Var(2),
                    Var(1)
                )
            )))),
            abs(Var(1))
        ))))
    )
}

/// Applied to two Church-encoded numbers it returns a Church-encoded remainder of their division.
/// It loops indefinitely if the second argument is `zero()`.
///
/// REM := Z (λzab.LT a b (λx.a) (λx.z (SUB a b) b) I) = Z (λ λ λ LT 2 1 (λ 3) (λ 4 (SUB 3 2) 2) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::rem;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(rem(), 3.into(), 2.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 1.into());
/// # }
/// ```
pub fn rem() -> Term {
    app(
        z(),
        abs(abs(abs(app!(
            Var(2),
            abs(abs(abs(app!(
                Var(3),
                abs(abs(app(Var(1), app(Var(2), Var(4))))),
                abs(Var(2)),
                abs(Var(1))
            )))),
            Var(1),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(Var(1))),
            abs(abs(Var(2))),
            abs(Var(3)),
            abs(app!(
                Var(4),
                app!(
                    Var(2),
                    abs(abs(abs(app!(
                        Var(3),
                        abs(abs(app(Var(1), app(Var(2), Var(4))))),
                        abs(Var(2)),
                        abs(Var(1))
                    )))),
                    Var(3)
                ),
                Var(2)
            )),
            abs(Var(1))
        ))))
    )
}

/// Applied to a Church-encoded number it yields its Church-encoded factorial.
///
/// FAC := λn. n (λfab. f (MULT a b) (SUCC b)) K ONE ONE =
/// λ 1 (λ λ λ 3 (MULT 2 1) (SUCC 1)) K ONE ONE
///
/// # Example
/// ```
/// use lambda_calculus::church::numerals::fac;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = fac().app(3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 6.into());
/// assert_eq!(beta(fac(), NOR, 0, false), fac());
/// ```
pub fn fac() -> Term {
    abs(app!(
        Var(1),
        abs(abs(abs(app!(
            Var(3),
            abs(app(Var(3), app(Var(2), Var(1)))),
            abs(abs(app(Var(2), app!(Var(3), Var(2), Var(1)))))
        )))),
        abs(abs(Var(2))),
        abs(abs(app(Var(2), Var(1)))),
        abs(abs(app(Var(2), Var(1))))
    ))
}

/// Applied to two Church-encoded numbers it returns their minimum.
///
/// MIN := λaλb.(LEQ a b) a b = λ λ (LEQ 2 1) 2 1
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::min;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(min(), 4.into(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 3.into());
/// assert_eq!(beta(min(), NOR, 0, false), min());
/// # }
/// ```
pub fn min() -> Term {
	abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        Var(2),
        Var(1)
    )))
}

/// Applied to two Church-encoded numbers it returns their maximum.
///
/// MAX := λaλb.(LEQ a b) b a = λ λ (LEQ 2 1) 1 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::max;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(max(), 4.into(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 4.into());
/// assert_eq!(beta(max(), NOR, 0, false), max());
/// # }
/// ```
pub fn max() -> Term {
	abs(abs(app!(
        Var(1),
        abs(abs(abs(
            app!(Var(3), abs(abs(app(Var(1), app(Var(2), Var(4))))), abs(Var(2)), abs(Var(1)))
        ))),
        Var(2),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        Var(1),
        Var(2)
    )))
}

/// Applied to two Church-encoded numbers `a` and `b` it returns the left [logical
/// shift](https://en.wikipedia.org/wiki/Logical_shift) of `a` performed `b` times.
///
/// LSHIFT := λaλb.MULT a (POW (SUCC ONE a)) = λ λ MULT 2 (POW (SUCC ONE) 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::lshift;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(lshift(), 3.into(), 2.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 12.into());
/// assert_eq!(beta(lshift(), NOR, 0, false), lshift());
/// # }
/// ```
pub fn lshift() -> Term {
    abs(abs(abs(app(
        Var(3),
        app!(
            Var(2),
            abs(abs(abs(Var(1)))),
            abs(abs(Var(2))),
            abs(abs(app(Var(2), Var(1)))),
            app(Var(2), abs(abs(app(Var(2), app(Var(2), Var(1)))))),
            Var(1)
        )
    ))))
}

/// Applied to two Church-encoded numbers `a` and `b` it returns the right [logical
/// shift](https://en.wikipedia.org/wiki/Logical_shift) of `a` performed `b` times.
///
/// RSHIFT := λaλb.(IS_ZERO b) a (QUOT a (POW (SUCC ONE) b)) =
/// λ λ (IS_ZERO 1) 2 (QUOT 2 (POW (SUCC ONE) 1))
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::rshift;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(rshift(), 6.into(), 1.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, 3.into());
/// # }
/// ```
pub fn rshift() -> Term {
    abs(abs(app!(
        Var(1),
        abs(abs(abs(Var(1)))),
        abs(abs(Var(2))),
        Var(2),
        app!(
            quot(),
            Var(2),
            app!(
                Var(1),
                abs(abs(abs(Var(1)))),
                abs(abs(Var(2))),
                abs(abs(app(Var(2), Var(1)))),
                app(Var(1), abs(abs(app(Var(2), app(Var(2), Var(1))))))
            )
        )
    )))
}

/// Applied to a Church-encoded number it produces a Church-encoded boolean, indicating whether its
/// argument is even.
///
/// IS_EVEN := NOT TRUE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::is_even;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(is_even(), 4.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, true.into());
/// assert_eq!(beta(is_even(), NOR, 0, false), is_even());
/// # }
/// ```
pub fn is_even() -> Term {
    abs(app!(Var(1), abs(app!(Var(1), fls(), tru())), tru()))
}

/// Applied to a Church-encoded number it produces a Church-encoded boolean, indicating whether its
/// argument is odd.
///
/// IS_ODD := NOT FALSE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::numerals::is_odd;
/// use lambda_calculus::reduction::*;
///
/// let mut expr = app!(is_odd(), 3.into());
/// expr.beta(NOR, 0, false);
///
/// assert_eq!(expr, true.into());
/// assert_eq!(beta(is_odd(), NOR, 0, false), is_odd());
/// # }
/// ```
pub fn is_odd() -> Term {
    abs(app!(Var(1), abs(app!(Var(1), fls(), tru())), fls()))
}

impl Term {
    /// Returns the value of `self` if it's a Church-encoded number.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::church::numerals::one;
    ///
    /// assert_eq!(one().value(), Ok(1));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church number.
    pub fn value(&self) -> Result<usize, Error> {
        if let Ok(inner) = self.unabs_ref().and_then(|t| t.unabs_ref()) {
            Ok(try!(inner._value()))
        } else {
            Err(NotANum)
        }
    }

    fn _value(&self) -> Result<usize, Error> {
        if let Ok((lhs, rhs)) = self.unapp_ref() {
            if *lhs == Var(2) {
                Ok(1 + try!(rhs._value()))
            } else {
                Err(NotANum)
            }
        } else if *self == Var(1) {
            Ok(0)
        } else {
            Err(NotANum)
        }
    }

    /// Checks whether `self` is a Church-encoded number.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::church::numerals::one;
    ///
    /// assert!(one().is_cnum());
    /// ```
    pub fn is_cnum(&self) -> bool { self.value().is_ok() }
}

impl From<usize> for Term {
    fn from(n: usize) -> Self {
        let mut inner = Var(1);
        let mut count = n;

        while count > 0 {
            inner = Var(2).app(inner);
            count -= 1;
        }

        abs(abs(inner))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use reduction::beta;
    use reduction::Order::*;
    use combinators::c;

    #[test]
    fn church_invalid_nums() {
        assert_eq!(      tru().is_cnum(), false);
        assert_eq!(     Var(1).is_cnum(), false);
        assert_eq!(abs(Var(1)).is_cnum(), false);
    }

    #[test]
    fn church_number_values() {
        for n in 0..10 { assert_eq!(Term::from(n).value(), Ok(n)) }
    }

    #[test]
    fn church_successor() {
        assert_eq!(beta(app!(succ(), 0.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), NOR, 0, false), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), HNO, 0, false), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), APP, 0, false), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), APP, 0, false), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), APP, 0, false), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), HAP, 0, false), 3.into());
    }

    #[test]
    fn church_predecessor() {
        assert_eq!(beta(app!(pred(), 0.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), NOR, 0, false), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), HNO, 0, false), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), APP, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), APP, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), APP, 0, false), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), HAP, 0, false), 4.into());
    }

    #[test]
    fn church_plus_sub_equivalents() {
        /* PLUS 1 → SUCC & C SUB 1 → PRED */
        assert_eq!(beta(app!(    plus(), 1.into()), NOR, 0, false), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), NOR, 0, false), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), HNO, 0, false), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), HNO, 0, false), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), APP, 0, false), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), APP, 0, false), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), HAP, 0, false), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), HAP, 0, false), pred());
    }

    #[test]
    fn church_multiplication() {
        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), NOR, 0, false), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), NOR, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), NOR, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), NOR, 0, false),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), NOR, 0, false),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), HNO, 0, false), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), HNO, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), HNO, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), HNO, 0, false),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), HNO, 0, false),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), APP, 0, false), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), APP, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), APP, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), APP, 0, false),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), APP, 0, false),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), HAP, 0, false), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), HAP, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), HAP, 0, false),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), HAP, 0, false),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), HAP, 0, false),  0.into());
    }

    #[test]
    fn church_exponentiation() {
        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), NOR, 0, false), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), NOR, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), NOR, 0, false),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), NOR, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), NOR, 0, false),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), HNO, 0, false), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), HNO, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), HNO, 0, false),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), HNO, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), HNO, 0, false),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), APP, 0, false), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), APP, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), APP, 0, false),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), APP, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), APP, 0, false),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), HAP, 0, false), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), HAP, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), HAP, 0, false),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), HAP, 0, false),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), HAP, 0, false),  0.into());
    }

    #[test]
    fn church_division() {
        assert_eq!(beta(app!(div(), 2.into(), 2.into()), NOR, 0, false), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), NOR, 0, false), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 5.into(), 2.into()), NOR, 0, false), (2.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), NOR, 0, false), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), NOR, 0, false), (0.into(), 0.into()).into());
     // assert_eq!(beta(app!(div(), 1.into(), 0.into()), NOR, 0, false), ); division by 0 hangs

        assert_eq!(beta(app!(div(), 2.into(), 2.into()), HNO, 0, false), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), HNO, 0, false), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 5.into(), 2.into()), HNO, 0, false), (2.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), HNO, 0, false), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), HNO, 0, false), (0.into(), 0.into()).into());

        assert_eq!(beta(app!(div(), 2.into(), 2.into()), HAP, 0, false), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), HAP, 0, false), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 5.into(), 2.into()), HAP, 0, false), (2.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), HAP, 0, false), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), HAP, 0, false), (0.into(), 0.into()).into());
    }

    #[test]
    fn church_quotient() {
        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 5.into(), 2.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), NOR, 0, false), 0.into());
    //  assert_eq!(beta(app!(quot(), 1.into(), 0.into()), NOR, 0, false), ); division by 0 hangs

        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 5.into(), 2.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), HNO, 0, false), 0.into());

        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(quot(), 5.into(), 2.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), HAP, 0, false), 0.into());
    }

    #[test]
    fn church_remainder() {
        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 5.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), NOR, 0, false), 0.into());
     // assert_eq!(beta(app!(rem(), 1.into(), 0.into()), NOR, 0, false), ); division by 0 hangs

        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 5.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), HNO, 0, false), 0.into());

        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 5.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), HAP, 0, false), 0.into());
    }

    #[test]
    fn church_factorial() {
        assert_eq!(beta(app!(fac(), 0.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 1.into()), NOR, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 2.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(fac(), 3.into()), NOR, 0, false), 6.into());

        assert_eq!(beta(app!(fac(), 0.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 1.into()), HNO, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 2.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(fac(), 3.into()), HNO, 0, false), 6.into());

        assert_eq!(beta(app!(fac(), 0.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 1.into()), HAP, 0, false), 1.into());
        assert_eq!(beta(app!(fac(), 2.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(fac(), 3.into()), HAP, 0, false), 6.into());
    }

    #[test]
    fn church_min() {
        assert_eq!(beta(app!(min(), 0.into(), 0.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(min(), 4.into(), 4.into()), NOR, 0, false), 4.into());
        assert_eq!(beta(app!(min(), 2.into(), 3.into()), NOR, 0, false), 2.into());
        assert_eq!(beta(app!(min(), 5.into(), 3.into()), NOR, 0, false), 3.into());
        assert_eq!(beta(app!(min(), 0.into(), 1.into()), NOR, 0, false), 0.into());

        assert_eq!(beta(app!(min(), 0.into(), 0.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(min(), 4.into(), 4.into()), HNO, 0, false), 4.into());
        assert_eq!(beta(app!(min(), 2.into(), 3.into()), HNO, 0, false), 2.into());
        assert_eq!(beta(app!(min(), 5.into(), 3.into()), HNO, 0, false), 3.into());
        assert_eq!(beta(app!(min(), 0.into(), 1.into()), HNO, 0, false), 0.into());

        assert_eq!(beta(app!(min(), 0.into(), 0.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(min(), 4.into(), 4.into()), HAP, 0, false), 4.into());
        assert_eq!(beta(app!(min(), 2.into(), 3.into()), HAP, 0, false), 2.into());
        assert_eq!(beta(app!(min(), 5.into(), 3.into()), HAP, 0, false), 3.into());
        assert_eq!(beta(app!(min(), 0.into(), 1.into()), HAP, 0, false), 0.into());
    }

    #[test]
    fn church_max() {
        assert_eq!(beta(app!(max(), 0.into(), 0.into()), NOR, 0, false), 0.into());
        assert_eq!(beta(app!(max(), 4.into(), 4.into()), NOR, 0, false), 4.into());
        assert_eq!(beta(app!(max(), 2.into(), 3.into()), NOR, 0, false), 3.into());
        assert_eq!(beta(app!(max(), 5.into(), 3.into()), NOR, 0, false), 5.into());
        assert_eq!(beta(app!(max(), 0.into(), 1.into()), NOR, 0, false), 1.into());

        assert_eq!(beta(app!(max(), 0.into(), 0.into()), HNO, 0, false), 0.into());
        assert_eq!(beta(app!(max(), 4.into(), 4.into()), HNO, 0, false), 4.into());
        assert_eq!(beta(app!(max(), 2.into(), 3.into()), HNO, 0, false), 3.into());
        assert_eq!(beta(app!(max(), 5.into(), 3.into()), HNO, 0, false), 5.into());
        assert_eq!(beta(app!(max(), 0.into(), 1.into()), HNO, 0, false), 1.into());

        assert_eq!(beta(app!(max(), 0.into(), 0.into()), HAP, 0, false), 0.into());
        assert_eq!(beta(app!(max(), 4.into(), 4.into()), HAP, 0, false), 4.into());
        assert_eq!(beta(app!(max(), 2.into(), 3.into()), HAP, 0, false), 3.into());
        assert_eq!(beta(app!(max(), 5.into(), 3.into()), HAP, 0, false), 5.into());
        assert_eq!(beta(app!(max(), 0.into(), 1.into()), HAP, 0, false), 1.into());
    }

    #[test]
    fn church_lshift() {
         assert_eq!(beta(app!(lshift(), 0.into(), 2.into()), NOR, 0, false), 0.into());
         assert_eq!(beta(app!(lshift(), 1.into(), 0.into()), NOR, 0, false), 1.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 0.into()), NOR, 0, false), 2.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 2.into()), NOR, 0, false), 8.into());
         assert_eq!(beta(app!(lshift(), 3.into(), 2.into()), NOR, 0, false), 12.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 3.into()), NOR, 0, false), 16.into());
         assert_eq!(beta(app!(lshift(), 5.into(), 1.into()), NOR, 0, false), 10.into());

         assert_eq!(beta(app!(lshift(), 0.into(), 2.into()), HNO, 0, false), 0.into());
         assert_eq!(beta(app!(lshift(), 1.into(), 0.into()), HNO, 0, false), 1.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 0.into()), HNO, 0, false), 2.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 2.into()), HNO, 0, false), 8.into());
         assert_eq!(beta(app!(lshift(), 3.into(), 2.into()), HNO, 0, false), 12.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 3.into()), HNO, 0, false), 16.into());
         assert_eq!(beta(app!(lshift(), 5.into(), 1.into()), HNO, 0, false), 10.into());

         assert_eq!(beta(app!(lshift(), 0.into(), 2.into()), HAP, 0, false), 0.into());
         assert_eq!(beta(app!(lshift(), 1.into(), 0.into()), HAP, 0, false), 1.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 0.into()), HAP, 0, false), 2.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 2.into()), HAP, 0, false), 8.into());
         assert_eq!(beta(app!(lshift(), 3.into(), 2.into()), HAP, 0, false), 12.into());
         assert_eq!(beta(app!(lshift(), 2.into(), 3.into()), HAP, 0, false), 16.into());
         assert_eq!(beta(app!(lshift(), 5.into(), 1.into()), HAP, 0, false), 10.into());
    }

    #[test]
    fn church_rshift() {
         assert_eq!(beta(app!(rshift(), 1.into(), 0.into()), NOR, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 0.into()), NOR, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 0.into(), 2.into()), NOR, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 1.into()), NOR, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 2.into()), NOR, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 5.into(), 1.into()), NOR, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 1.into()), NOR, 0, false), 4.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 2.into()), NOR, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 7.into(), 1.into()), NOR, 0, false), 3.into());

         assert_eq!(beta(app!(rshift(), 1.into(), 0.into()), HNO, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 0.into()), HNO, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 0.into(), 2.into()), HNO, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 1.into()), HNO, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 2.into()), HNO, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 5.into(), 1.into()), HNO, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 1.into()), HNO, 0, false), 4.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 2.into()), HNO, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 7.into(), 1.into()), HNO, 0, false), 3.into());

         assert_eq!(beta(app!(rshift(), 1.into(), 0.into()), HAP, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 0.into()), HAP, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 0.into(), 2.into()), HAP, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 1.into()), HAP, 0, false), 1.into());
         assert_eq!(beta(app!(rshift(), 2.into(), 2.into()), HAP, 0, false), 0.into());
         assert_eq!(beta(app!(rshift(), 5.into(), 1.into()), HAP, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 1.into()), HAP, 0, false), 4.into());
         assert_eq!(beta(app!(rshift(), 9.into(), 2.into()), HAP, 0, false), 2.into());
         assert_eq!(beta(app!(rshift(), 7.into(), 1.into()), HAP, 0, false), 3.into());
    }

    #[test]
    fn church_is_even() {
         assert_eq!(beta(app!(is_even(), 0.into()), NOR, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 1.into()), NOR, 0, false), false.into());
         assert_eq!(beta(app!(is_even(), 2.into()), NOR, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 8.into()), NOR, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 9.into()), NOR, 0, false), false.into());

         assert_eq!(beta(app!(is_even(), 0.into()), HNO, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 1.into()), HNO, 0, false), false.into());
         assert_eq!(beta(app!(is_even(), 2.into()), HNO, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 8.into()), HNO, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 9.into()), HNO, 0, false), false.into());

         assert_eq!(beta(app!(is_even(), 0.into()), HAP, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 1.into()), HAP, 0, false), false.into());
         assert_eq!(beta(app!(is_even(), 2.into()), HAP, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 8.into()), HAP, 0, false), true.into());
         assert_eq!(beta(app!(is_even(), 9.into()), HAP, 0, false), false.into());
    }

    #[test]
    fn church_is_odd() {
         assert_eq!(beta(app!(is_odd(), 0.into()), NOR, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 1.into()), NOR, 0, false), true.into());
         assert_eq!(beta(app!(is_odd(), 2.into()), NOR, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 8.into()), NOR, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 9.into()), NOR, 0, false), true.into());

         assert_eq!(beta(app!(is_odd(), 0.into()), HNO, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 1.into()), HNO, 0, false), true.into());
         assert_eq!(beta(app!(is_odd(), 2.into()), HNO, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 8.into()), HNO, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 9.into()), HNO, 0, false), true.into());

         assert_eq!(beta(app!(is_odd(), 0.into()), HAP, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 1.into()), HAP, 0, false), true.into());
         assert_eq!(beta(app!(is_odd(), 2.into()), HAP, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 8.into()), HAP, 0, false), false.into());
         assert_eq!(beta(app!(is_odd(), 9.into()), HAP, 0, false), true.into());
    }
}
