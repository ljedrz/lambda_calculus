//! [Church-encoded numerals](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals) and
//! arithmetic operations

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;
//use pair::pair;
//use combinators::y;

/// Produces a Church-encoded number zero.
///
/// ZERO := λfx.x = λ λ 1
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::zero;
///
/// assert_eq!(format!("{}", zero()), "λλ1");
/// ```
pub fn zero() -> Term { abs(abs(Var(1))) }

/// Applied to a Church-encoded number it produces a Church-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// IS_ZERO := λn.n (λx.FALSE) TRUE =  λ 1 (λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, is_zero};
/// use lambda_calculus::booleans::tru;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(is_zero().app(zero())), tru());
/// ```
pub fn is_zero() -> Term {
    abs(
        Var(1)
        .app(abs(fls()))
        .app(tru())
    )
}

/// Produces a Church-encoded number one.
///
/// ONE := λfx.f x = λ λ 2 1
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::one;
///
/// assert_eq!(format!("{}", one()), "λλ21");
/// ```
pub fn one() -> Term {
    abs(abs(
        Var(2).app(Var(1))
    ))
}

/// Applied to a Church-encoded number it produces its successor.
///
/// SUCC := λnfx.f (n f x) = λ λ λ 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, succ};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(succ().app(zero())), one());
/// ```
pub fn succ() -> Term {
    abs(abs(abs(
        Var(2).app(
            Var(3)
            .app(Var(2))
            .app(Var(1))
        )
    )))
}

/// Applied to two Church-encoded numbers it produces their sum.
///
/// PLUS := λmnfx.m f (n f x) = λ λ λ λ 4 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, plus};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(plus().app(zero()).app(one())), one());
/// ```
pub fn plus() -> Term {
    abs(abs(abs(abs(
        Var(4)
        .app(Var(2))
        .app(Var(3).app(Var(2)).app(Var(1)))
    ))))
}

/// Applied to two Church-encoded numbers it produces their product.
///
/// MULT := λmnf.m (n f) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, mult};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(mult().app(one()).app(one())), one());
/// ```
pub fn mult() -> Term {
    abs(abs(abs(
        Var(3).app(Var(2).app(Var(1)))
    )))
}

/// Applied to two Church-encoded numbers it raises the first one to the power of the second one.
///
/// POW := λbe.e b = λ λ 1 2
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, pow};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(pow().app(one()).app(one())), one());
/// ```
pub fn pow() -> Term {
    abs(abs(
        Var(1).app(Var(2))
    ))
}

/// Applied to a Church-encoded number it produces its predecessor.
///
/// PRED := λnfx.n (λgh.h (g f)) (λu.x) (λu.u) = λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, pred};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(pred().app(one())), zero());
/// ```
pub fn pred() -> Term {
    abs(abs(abs(
        Var(3)
        .app(abs(abs(Var(1).app(Var(2).app(Var(4))))))
        .app(abs(Var(2)))
        .app(abs(Var(1)))
    )))
}

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// SUB := λmn.n PRED m = λ λ 1 PRED 2
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, sub};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(sub().app(one()).app(zero())), one());
/// ```
pub fn sub() -> Term {
    abs(abs(
        Var(1).app(pred()).app(Var(2))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is less than the second one.
///
/// LT := λab.NOT (LEQ b a) = λ λ NOT (LEQ 1 2)
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, lt};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(lt().app(zero()).app(zero())), fls());
/// assert_eq!(normalize(lt().app(one()).app(one())),   fls());
/// assert_eq!(normalize(lt().app(zero()).app(one())),  tru());
/// assert_eq!(normalize(lt().app(one()).app(zero())),  fls());
/// ```
pub fn lt() -> Term {
    abs(abs(
        not().app(leq().app(Var(1)).app(Var(2)))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is less than or egual to the second one.
///
/// LEQ := λmn.IS_ZERO (SUB m n) = λ λ IS_ZERO (SUB 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, leq};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(leq().app(zero()).app(zero())), tru());
/// assert_eq!(normalize(leq().app(one()).app(one())),   tru());
/// assert_eq!(normalize(leq().app(zero()).app(one())),  tru());
/// assert_eq!(normalize(leq().app(one()).app(zero())),  fls());
/// ```
pub fn leq() -> Term {
    abs(abs(
        is_zero().app(sub().app(Var(2)).app(Var(1)))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is egual to the second one.
///
/// EQ := λmn.AND (LEQ m n) (LEQ n m) = λ λ AND (LEQ 2 1) (LEQ 1 2)
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, eq};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(eq().app(zero()).app(zero())), tru());
/// assert_eq!(normalize(eq().app(one()).app(one())),   tru());
/// assert_eq!(normalize(eq().app(zero()).app(one())),  fls());
/// assert_eq!(normalize(eq().app(one()).app(zero())),  fls());
/// ```
pub fn eq() -> Term {
    abs(abs(
        and()
        .app(leq().app(Var(2)).app(Var(1)))
        .app(leq().app(Var(1)).app(Var(2)))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is not egual to the second one.
///
/// NEQ := λab.OR (NOT (LEQ a b)) (NOT (LEQ b a)) = λ λ OR (NOT (LEQ 2 1)) (NOT (LEQ 1 2))
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, neq};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(neq().app(zero()).app(zero())), fls());
/// assert_eq!(normalize(neq().app(one()).app(one())),   fls());
/// assert_eq!(normalize(neq().app(zero()).app(one())),  tru());
/// assert_eq!(normalize(neq().app(one()).app(zero())),  tru());
/// ```
pub fn neq() -> Term {
    abs(abs(
        or()
        .app(not().app(leq().app(Var(2)).app(Var(1))))
        .app(not().app(leq().app(Var(1)).app(Var(2))))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is greater than or egual to the second one.
///
/// GEQ := λab.LEQ b a = λ λ LEQ 1 2
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, geq};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(geq().app(zero()).app(zero())), tru());
/// assert_eq!(normalize(geq().app(one()).app(one())),   tru());
/// assert_eq!(normalize(geq().app(zero()).app(one())),  fls());
/// assert_eq!(normalize(geq().app(one()).app(zero())),  tru());
/// ```
pub fn geq() -> Term {
    abs(abs(
        leq().app(Var(1)).app(Var(2))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether
/// its first argument is greater than the second one.
///
/// GT := λab.NOT (LEQ a b) = λ λ NOT (LEQ 2 1)
///
/// # Examples
/// ```
/// use lambda_calculus::arithmetic::{zero, one, gt};
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(gt().app(zero()).app(zero())), fls());
/// assert_eq!(normalize(gt().app(one()).app(one())),   fls());
/// assert_eq!(normalize(gt().app(zero()).app(one())),  fls());
/// assert_eq!(normalize(gt().app(one()).app(zero())),  tru());
/// ```
pub fn gt() -> Term {
    abs(abs(
        not().app(leq().app(Var(2)).app(Var(1)))
    ))
}
/*
// FIXME: blows up RAM
/// Applied to two Church-encoded numbers it returns a Church-encoded pair with the result of their
/// division - the quotient and the remainder.
///
/// DIV := Y (λgqab.LT a b (PAIR q a) (g (SUCC q) (SUB a b) b)) ZERO =
/// Y (λ λ λ λ LT 2 1 (PAIR 3 2) (4 (SUCC 3) (SUB 2 1) 1)) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{div, one, to_cnum};
/// use lambda_calculus::pair::pair;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(div().app(to_cnum(5)).app(to_cnum(2))),
///            normalize(pair().app(to_cnum(2)).app(one())));
/// ```
pub fn div() -> Term {
    y()
    .app(
        abs(abs(abs(abs(
            lt()
            .app(Var(2))
            .app(Var(1))
            .app(pair().app(Var(3)).app(Var(2)))
            .app(
                Var(4)
                .app(succ().app(Var(3)))
                .app(sub().app(Var(2)).app(Var(1)))
                .app(Var(1))
            )
        ))))
    )
    .app(zero())
}
*/

/*
// FIXME: blows up RAM
/// Applied to two Church-encoded numbers it returns a Church-encoded quotient of their division.
///
/// QUOT := y (λrab.LT a b ZERO (SUCC (r (SUB a b) b)))
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{quot, to_cnum};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(quot().app(to_cnum(6)).app(to_cnum(2))), to_cnum(3));
/// ```
pub fn quot() -> Term {
    y().app(
        abs(abs(abs(
            lt()
            .app(Var(2))
            .app(Var(1))
            .app(zero())
            .app(
                succ().app(
                    Var(3)
                    .app(
                        sub()
                        .app(Var(2))
                        .app(Var(1))
                    )
                    .app(Var(1))
                )
            )
        )))
    )
}
*/
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
        if let Ok(ref rhs) = self.rhs_ref() {
            Ok(1 + try!(rhs._value()))
        } else if let Var(n) = *self {
            if n == 1 {
                Ok(0)
            } else {
                Err(NotANum)
            }
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
    use reduction::normalize;

    #[test]
    fn church_zero() {
        assert_eq!(normalize(is_zero().app(zero())), tru());
        assert_eq!(normalize(is_zero().app(one())), fls());
    }

    #[test]
    fn church_successor() {
        assert_eq!(normalize(succ().app(zero())), one());
        assert_eq!(normalize(succ().app(one())), abs(abs(Var(2).app(Var(2).app(Var(1))))));
        assert_eq!(normalize(succ().app(succ().app(succ().app(zero())))),
                   abs(abs(Var(2).app(Var(2).app(Var(2).app(Var(1)))))));
    }

    #[test]
    fn church_number_identification() {
        for n in 0..5 { assert!(Term::from(n).is_cnum()) }
    }

    #[test]
    fn church_number_creation() {
        assert_eq!(Term::from(0), zero());
        assert_eq!(Term::from(1), one());
        assert_eq!(Term::from(2), normalize(succ().app(one())));
    }

    #[test]
    fn church_number_values() {
        for n in 0..10 { assert_eq!(Term::from(n).value(), Ok(n)) }

        assert_eq!(tru().value(),       Err(NotANum));
        assert_eq!(Var(1).value(),      Err(NotANum));
        assert_eq!(abs(Var(1)).value(), Err(NotANum));
    }

    #[test]
    fn church_addition() {
        assert_eq!(normalize(plus().app(1.into())), succ()); // PLUS 1 → SUCC

        assert_eq!(normalize(plus().app(0.into()).app(0.into())), 0.into());
        assert_eq!(normalize(plus().app(0.into()).app(1.into())), 1.into());
        assert_eq!(normalize(plus().app(1.into()).app(0.into())), 1.into());
        assert_eq!(normalize(plus().app(1.into()).app(1.into())), 2.into());

        assert_eq!(normalize(plus().app(2.into()).app(3.into())), 5.into());
        assert_eq!(normalize(plus().app(4.into()).app(4.into())), 8.into());
    }

    #[test]
    fn church_multiplication() {
        assert_eq!(normalize(mult().app(3.into()).app(4.into())), 12.into());
        assert_eq!(normalize(mult().app(1.into()).app(3.into())), 3.into());
        assert_eq!(normalize(mult().app(5.into()).app(0.into())), 0.into());
    }

    #[test]
    fn church_exponentiation() {
        assert_eq!(normalize(pow().app(2.into()).app(4.into())), 16.into());
        assert_eq!(normalize(pow().app(1.into()).app(6.into())), 1.into());
        assert_eq!(normalize(pow().app(3.into()).app(2.into())), 9.into());
        assert_eq!(normalize(pow().app(4.into()).app(1.into())), 4.into());
//      assert_eq!(normalize(pow().app(5.into()).app(0.into())), 1.into()); // n^0 fails
    }

    #[test]
    fn church_subtraction() {
        assert_eq!(normalize(sub().app(0.into()).app(0.into())), 0.into());
        assert_eq!(normalize(sub().app(0.into()).app(1.into())), 0.into());
        assert_eq!(normalize(sub().app(1.into()).app(0.into())), 1.into());
        assert_eq!(normalize(sub().app(2.into()).app(1.into())), 1.into());

        assert_eq!(normalize(sub().app(5.into()).app(3.into())), 2.into());
        assert_eq!(normalize(sub().app(8.into()).app(4.into())), 4.into());
    }

    #[test]
    fn church_predecessor() {
        assert_eq!(normalize(pred().app(0.into())), 0.into());
        assert_eq!(normalize(pred().app(1.into())), 0.into());
        assert_eq!(normalize(pred().app(5.into())), 4.into());
    }
}
