//! [Church-encoded numerals](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals) and
//! arithmetic operations

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;
use pair::{pair, second};
use combinators::{i, k, z};

/// Produces a Church-encoded number zero.
///
/// ZERO := λfx.x = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::zero;
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
/// use lambda_calculus::arithmetic::is_zero;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(is_zero(), 0.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(is_zero(), 1.into()), &Normal, 0), fls());
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
/// use lambda_calculus::arithmetic::one;
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
/// use lambda_calculus::arithmetic::succ;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = succ().app(0.into());
/// expr.beta(&Normal, 0);
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
/// use lambda_calculus::arithmetic::plus;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(plus(), 3.into(), 2.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 5.into());
/// # }
/// ```
pub fn plus() -> Term {
    abs(abs(abs(abs(
        app!(Var(4), Var(2), app!(Var(3), Var(2), Var(1)))
    ))))
}

/// Applied to two Church-encoded numbers it produces their product.
///
/// MULT := λmnf.m (n f) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::mult;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(mult(), 2.into(), 3.into());
/// expr.beta(&Normal, 0);
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
/// POW := λbe.IS_ZERO e ONE (e b) = λ λ IS_ZERO 1 ONE (1 2)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::pow;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(pow(), 2.into(), 3.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 8.into());
/// # }
/// ```
pub fn pow() -> Term {
    abs(abs(
        app!(is_zero(), Var(1), one(), app(Var(1), Var(2)))
    ))
}

/// Applied to a Church-encoded number it produces its predecessor.
///
/// PRED := λnfx.n (λgh.h (g f)) (λu.x) (λu.u) = λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::pred;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = pred().app(3.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 2.into());
/// ```
pub fn pred() -> Term {
    abs(abs(abs(
        app!(
            Var(3),
            abs(abs(app(Var(1), app(Var(2), Var(4))))),
            abs(Var(2)),
            abs(Var(1))
        )
    )))
}

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// SUB := λmn.n PRED m = λ λ 1 PRED 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::sub;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(sub(), 5.into(), 3.into());
/// expr.beta(&Normal, 0);
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
/// use lambda_calculus::arithmetic::lt;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(lt(), 0.into(), 0.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(lt(), 1.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(lt(), 0.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(lt(), 1.into(), 0.into()), &Normal, 0), fls());
/// # }
/// ```
pub fn lt() -> Term {
    abs(abs(
        app(not(), app!(leq(), Var(1), Var(2)))
    ))
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
/// use lambda_calculus::arithmetic::leq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(leq(), 0.into(), 0.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(leq(), 1.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(leq(), 0.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(leq(), 1.into(), 0.into()), &Normal, 0), fls());
/// # }
/// ```
pub fn leq() -> Term {
    abs(abs(
        app(is_zero(), app!(sub(), Var(2), Var(1)))
    ))
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
/// use lambda_calculus::arithmetic::eq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(eq(), 0.into(), 0.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(eq(), 1.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(eq(), 0.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(eq(), 1.into(), 0.into()), &Normal, 0), fls());
/// # }
/// ```
pub fn eq() -> Term {
    abs(abs(
        app!(
            and(),
            app!(leq(), Var(2), Var(1)),
            app!(leq(), Var(1), Var(2))
        )
    ))
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
/// use lambda_calculus::arithmetic::neq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(neq(), 0.into(), 0.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(neq(), 1.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(neq(), 0.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(neq(), 1.into(), 0.into()), &Normal, 0), tru());
/// # }
/// ```
pub fn neq() -> Term {
    abs(abs(
        app!(
            or(),
            app(not(), app!(leq(), Var(2), Var(1))),
            app(not(), app!(leq(), Var(1), Var(2)))
        )
    ))
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
/// use lambda_calculus::arithmetic::geq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(geq(), 0.into(), 0.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(geq(), 1.into(), 1.into()), &Normal, 0), tru());
/// assert_eq!(beta(app!(geq(), 0.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(geq(), 1.into(), 0.into()), &Normal, 0), tru());
/// # }
/// ```
pub fn geq() -> Term {
    abs(abs(
        app!(leq(), Var(1), Var(2))
    ))
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
/// use lambda_calculus::arithmetic::{zero, one, gt};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(gt(), 0.into(), 0.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(gt(), 1.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(gt(), 0.into(), 1.into()), &Normal, 0), fls());
/// assert_eq!(beta(app!(gt(), 1.into(), 0.into()), &Normal, 0), tru());
/// # }
/// ```
pub fn gt() -> Term {
    abs(abs(
        app(not(), app!(leq(), Var(2), Var(1)))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded pair with the result of their
/// division - the quotient and the remainder. It loops indefinitely if the divisor is `zero()`.
///
/// DIV := Z (λgqab.LT a b (λx.PAIR q a) (λx.g (SUCC q) (SUB a b) b) I) ZERO =
/// Z (λ λ λ λ LT 2 1 (λ PAIR 4 3) (λ 5 (SUCC 4) (SUB 3 2) 2) I) ZERO
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::div;
/// use lambda_calculus::term::Term;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(div(), 5.into(), 2.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, Term::from((2.into(), 1.into())));
/// # }
/// ```
pub fn div() -> Term {
    app!(
        z(),
        abs(abs(abs(abs(
            app!(
                lt(),
                Var(2),
                Var(1),
                abs(app!(pair(), Var(4), Var(3))),
                abs(app!(
                    Var(5),
                    app(succ(), Var(4)),
                    app!(sub(), Var(3), Var(2)),
                    Var(2)
                )),
                i()
            )
        )))),
        zero()
    )
}

/// Applied to two Church-encoded numbers it returns a Church-encoded quotient of their division.
/// It loops indefinitely if the second argument is `zero()`.
///
/// QUOT := Z (λrab.LT a b (λx.ZERO) (λx.SUCC (r (SUB a b) b)) I) =
/// Z (λ λ λ LT 2 1 (λ ZERO) (λ SUCC (4 (SUB 3 2) 2)) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::quot;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(quot(), 6.into(), 2.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 3.into());
/// # }
/// ```
pub fn quot() -> Term {
    app(
        z(),
        abs(abs(abs(
            app!(
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
                i()
            )
        )))
    )
}

// TODO: find an independent variant, like with quot()
/// Applied to two Church-encoded numbers it returns a Church-encoded remainder of their division.
/// It loops indefinitely if the second argument is `zero()`.
///
/// REM := λab. SECOND (DIV a b) = λ λ SECOND (DIV 2 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::arithmetic::rem;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = app!(rem(), 3.into(), 2.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 1.into());
/// # }
/// ```
pub fn rem() -> Term {
    abs(abs(
        app(second(), app!(div(), Var(2), Var(1)))
    ))
}

/// Applied to a Church-encoded number it yields its Church-encoded factorial.
///
/// FACTORIAL := λn. n (λfax. f (MULT a x) (SUCC x)) K ONE ONE =
/// λ 1 (λ λ λ 3 (MULT 2 1) (SUCC 1)) K ONE ONE
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::factorial;
/// use lambda_calculus::reduction::Order::*;
///
/// let mut expr = factorial().app(3.into());
/// expr.beta(&Normal, 0);
///
/// assert_eq!(expr, 6.into());
/// ```
pub fn factorial() -> Term {
    abs(
        app!(
            Var(1),
            abs(abs(abs(
                app!(
                    Var(3),
                    app!(mult(), Var(2), Var(1)),
                    app!(succ(), Var(1))
                )
            ))),
            k(),
            one(),
            one()
        )
    )
}

impl Term {
    /// Returns the value of `self` if it's a Church-encoded number.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::arithmetic::one;
    ///
    /// assert_eq!(one().value(), Ok(1));
    /// ```
    pub fn value(&self) -> Result<usize, Error> {
        if let Ok(ref inner) = self.unabs_ref().and_then(|t| t.unabs_ref()) {
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
    /// use lambda_calculus::arithmetic::one;
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
mod test {
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
        assert_eq!(beta(app!(succ(), 0.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), &Normal, 0), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), &Normal, 0), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), &HybridNormal, 0), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), &HybridNormal, 0), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), &Applicative, 0), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), &Applicative, 0), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), &Applicative, 0), 3.into());

        assert_eq!(beta(app!(succ(), 0.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(succ(), 1.into()), &HybridApplicative, 0), 2.into());
        assert_eq!(beta(app!(succ(), 2.into()), &HybridApplicative, 0), 3.into());
    }

    #[test]
    fn church_predecessor() {
        assert_eq!(beta(app!(pred(), 0.into()), &Normal, 0), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), &Normal, 0), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), &Normal, 0), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), &HybridNormal, 0), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), &HybridNormal, 0), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), &HybridNormal, 0), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), &Applicative, 0), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), &Applicative, 0), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), &Applicative, 0), 4.into());

        assert_eq!(beta(app!(pred(), 0.into()), &HybridApplicative, 0), 0.into());
        assert_eq!(beta(app!(pred(), 1.into()), &HybridApplicative, 0), 0.into());
        assert_eq!(beta(app!(pred(), 5.into()), &HybridApplicative, 0), 4.into());
    }

    #[test]
    fn church_plus_sub_equivalents() {
        /* PLUS 1 → SUCC & C SUB 1 → PRED */
        assert_eq!(beta(app!(    plus(), 1.into()), &Normal, 0), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), &Normal, 0), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), &HybridNormal, 0), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), &HybridNormal, 0), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), &Applicative, 0), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), &Applicative, 0), pred());

        assert_eq!(beta(app!(    plus(), 1.into()), &HybridApplicative, 0), succ());
        assert_eq!(beta(app!(c(), sub(), 1.into()), &HybridApplicative, 0), pred());
    }

    #[test]
    fn church_multiplication() {
        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), &Normal, 0), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), &Normal, 0),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), &Normal, 0),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), &Normal, 0),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), &Normal, 0),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), &HybridNormal, 0), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), &HybridNormal, 0),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), &HybridNormal, 0),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), &HybridNormal, 0),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), &HybridNormal, 0),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), &Applicative, 0), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), &Applicative, 0),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), &Applicative, 0),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), &Applicative, 0),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), &Applicative, 0),  0.into());

        assert_eq!(beta(app!(mult(), 3.into(), 4.into()), &HybridApplicative, 0), 12.into());
        assert_eq!(beta(app!(mult(), 1.into(), 3.into()), &HybridApplicative, 0),  3.into());
        assert_eq!(beta(app!(mult(), 3.into(), 1.into()), &HybridApplicative, 0),  3.into());
        assert_eq!(beta(app!(mult(), 5.into(), 0.into()), &HybridApplicative, 0),  0.into());
        assert_eq!(beta(app!(mult(), 0.into(), 5.into()), &HybridApplicative, 0),  0.into());
    }

    #[test]
    fn church_exponentiation() {
        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), &Normal, 0), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), &Normal, 0),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), &Normal, 0),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), &Normal, 0),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), &Normal, 0),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), &HybridNormal, 0), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), &HybridNormal, 0),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), &HybridNormal, 0),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), &HybridNormal, 0),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), &HybridNormal, 0),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), &Applicative, 0), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), &Applicative, 0),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), &Applicative, 0),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), &Applicative, 0),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), &Applicative, 0),  0.into());

        assert_eq!(beta(app!(pow(), 2.into(), 4.into()), &HybridApplicative, 0), 16.into());
        assert_eq!(beta(app!(pow(), 1.into(), 3.into()), &HybridApplicative, 0),  1.into());
        assert_eq!(beta(app!(pow(), 3.into(), 1.into()), &HybridApplicative, 0),  3.into());
        assert_eq!(beta(app!(pow(), 5.into(), 0.into()), &HybridApplicative, 0),  1.into());
        assert_eq!(beta(app!(pow(), 0.into(), 5.into()), &HybridApplicative, 0),  0.into());
    }

    #[test]
    fn church_division() {
        assert_eq!(beta(app!(div(), 2.into(), 2.into()), &Normal, 0), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), &Normal, 0), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), &Normal, 0), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), &Normal, 0), (0.into(), 0.into()).into());
     // assert_eq!(beta(app!(div(), 1.into(), 0.into()), &Normal, 0), ); division by 0 hangs

        assert_eq!(beta(app!(div(), 2.into(), 2.into()), &HybridNormal, 0), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), &HybridNormal, 0), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), &HybridNormal, 0), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), &HybridNormal, 0), (0.into(), 0.into()).into());

        assert_eq!(beta(app!(div(), 2.into(), 2.into()), &HybridApplicative, 0), (1.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 3.into(), 2.into()), &HybridApplicative, 0), (1.into(), 1.into()).into());
        assert_eq!(beta(app!(div(), 2.into(), 1.into()), &HybridApplicative, 0), (2.into(), 0.into()).into());
        assert_eq!(beta(app!(div(), 0.into(), 3.into()), &HybridApplicative, 0), (0.into(), 0.into()).into());
    }

    #[test]
    fn church_quotient() {
        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), &Normal, 0), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), &Normal, 0), 0.into());
    //  assert_eq!(beta(app!(quot(), 1.into(), 0.into()), &Normal, 0), ); division by 0 hangs

        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), &HybridNormal, 0), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), &HybridNormal, 0), 0.into());

        assert_eq!(beta(app!(quot(), 2.into(), 2.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(quot(), 3.into(), 2.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(quot(), 2.into(), 1.into()), &HybridApplicative, 0), 2.into());
        assert_eq!(beta(app!(quot(), 0.into(), 3.into()), &HybridApplicative, 0), 0.into());
    }

    #[test]
    fn church_remainder() {
        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), &Normal, 0), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), &Normal, 0), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), &Normal, 0), 0.into());
     // assert_eq!(beta(app!(rem(), 1.into(), 0.into()), &Normal, 0), ); division by 0 hangs

        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), &HybridNormal, 0), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), &HybridNormal, 0), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), &HybridNormal, 0), 0.into());

        assert_eq!(beta(app!(rem(), 2.into(), 2.into()), &HybridApplicative, 0), 0.into());
        assert_eq!(beta(app!(rem(), 3.into(), 2.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(rem(), 2.into(), 1.into()), &HybridApplicative, 0), 0.into());
        assert_eq!(beta(app!(rem(), 0.into(), 3.into()), &HybridApplicative, 0), 0.into());
    }

    #[test]
    fn church_factorial() {
        assert_eq!(beta(app!(factorial(), 0.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 1.into()), &Normal, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 2.into()), &Normal, 0), 2.into());
        assert_eq!(beta(app!(factorial(), 3.into()), &Normal, 0), 6.into());

        assert_eq!(beta(app!(factorial(), 0.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 1.into()), &HybridNormal, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 2.into()), &HybridNormal, 0), 2.into());
        assert_eq!(beta(app!(factorial(), 3.into()), &HybridNormal, 0), 6.into());

        assert_eq!(beta(app!(factorial(), 0.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 1.into()), &HybridApplicative, 0), 1.into());
        assert_eq!(beta(app!(factorial(), 2.into()), &HybridApplicative, 0), 2.into());
        assert_eq!(beta(app!(factorial(), 3.into()), &HybridApplicative, 0), 6.into());
    }
}
