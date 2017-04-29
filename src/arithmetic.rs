//! [Church-encoded numerals](https://en.wikipedia.org/wiki/Church_encoding#Church_numerals) and
//! arithmetic operations

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;
use pair::{pair, second};
use combinators::y;

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
/// use lambda_calculus::arithmetic::is_zero;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(is_zero().app(0.into())), tru());
/// assert_eq!(beta_full(is_zero().app(1.into())), fls());
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
/// use lambda_calculus::term::Term;
///
/// assert_eq!(one(), Term::from(1));
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
/// use lambda_calculus::arithmetic::succ;
///
/// let mut expr = succ().app(0.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 1.into());
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
/// use lambda_calculus::arithmetic::plus;
///
/// let mut expr = plus().app(3.into()).app(2.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 5.into());
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
/// use lambda_calculus::arithmetic::mult;
///
/// let mut expr = mult().app(2.into()).app(3.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 6.into());
/// ```
pub fn mult() -> Term {
    abs(abs(abs(
        Var(3).app(Var(2).app(Var(1)))
    )))
}

/// Applied to two Church-encoded numbers it raises the first one to the power of the second one.
///
/// POW := λbe.IF_ELSE (IS_ZERO e) ONE (e b) = λ λ IF_ELSE (IS_ZERO 1) ONE (1 2)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::pow;
///
/// let mut expr = pow().app(2.into()).app(3.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 8.into());
/// ```
pub fn pow() -> Term {
    abs(abs(
        if_else()
        .app(is_zero().app(Var(1)))
        .app(one())
        .app(Var(1).app(Var(2)))
    ))
}

/// Applied to a Church-encoded number it produces its predecessor.
///
/// PRED := λnfx.n (λgh.h (g f)) (λu.x) (λu.u) = λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::pred;
///
/// let mut expr = pred().app(3.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 2.into());
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
/// use lambda_calculus::arithmetic::sub;
///
/// let mut expr = sub().app(5.into()).app(3.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 2.into());
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
/// use lambda_calculus::arithmetic::lt;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(lt().app(0.into()).app(0.into())), fls());
/// assert_eq!(beta_full(lt().app(1.into()).app(1.into())), fls());
/// assert_eq!(beta_full(lt().app(0.into()).app(1.into())), tru());
/// assert_eq!(beta_full(lt().app(1.into()).app(0.into())), fls());
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
/// use lambda_calculus::arithmetic::leq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(leq().app(0.into()).app(0.into())), tru());
/// assert_eq!(beta_full(leq().app(1.into()).app(1.into())), tru());
/// assert_eq!(beta_full(leq().app(0.into()).app(1.into())), tru());
/// assert_eq!(beta_full(leq().app(1.into()).app(0.into())), fls());
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
/// use lambda_calculus::arithmetic::eq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(eq().app(0.into()).app(0.into())), tru());
/// assert_eq!(beta_full(eq().app(1.into()).app(1.into())), tru());
/// assert_eq!(beta_full(eq().app(0.into()).app(1.into())), fls());
/// assert_eq!(beta_full(eq().app(1.into()).app(0.into())), fls());
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
/// use lambda_calculus::arithmetic::neq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(neq().app(0.into()).app(0.into())), fls());
/// assert_eq!(beta_full(neq().app(1.into()).app(1.into())), fls());
/// assert_eq!(beta_full(neq().app(0.into()).app(1.into())), tru());
/// assert_eq!(beta_full(neq().app(1.into()).app(0.into())), tru());
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
/// use lambda_calculus::arithmetic::geq;
/// use lambda_calculus::booleans::{tru, fls};
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(geq().app(0.into()).app(0.into())), tru());
/// assert_eq!(beta_full(geq().app(1.into()).app(1.into())), tru());
/// assert_eq!(beta_full(geq().app(0.into()).app(1.into())), fls());
/// assert_eq!(beta_full(geq().app(1.into()).app(0.into())), tru());
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
/// use lambda_calculus::reduction::beta_full;
///
/// assert_eq!(beta_full(gt().app(0.into()).app(0.into())), fls());
/// assert_eq!(beta_full(gt().app(1.into()).app(1.into())), fls());
/// assert_eq!(beta_full(gt().app(0.into()).app(1.into())), fls());
/// assert_eq!(beta_full(gt().app(1.into()).app(0.into())), tru());
/// ```
pub fn gt() -> Term {
    abs(abs(
        not().app(leq().app(Var(2)).app(Var(1)))
    ))
}

/// Applied to two Church-encoded numbers it returns a Church-encoded pair with the result of their
/// division - the quotient and the remainder.
///
/// DIV := Y (λgqab.LT a b (PAIR q a) (g (SUCC q) (SUB a b) b)) ZERO =
/// Y (λ λ λ λ LT 2 1 (PAIR 3 2) (4 (SUCC 3) (SUB 2 1) 1)) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::div;
/// use lambda_calculus::term::Term;
///
/// let mut expr = div().app(5.into()).app(2.into());
/// expr.beta_full();
///
/// assert_eq!(expr, Term::from((2.into(), 1.into())));
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

/// Applied to two Church-encoded numbers it returns a Church-encoded quotient of their division.
///
/// QUOT := Y (λrab.LT a b ZERO (SUCC (r (SUB a b) b))) =
/// Y (λ λ λ LT 2 1 ZERO (SUCC (3 (SUB 2 1) 1)))
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::quot;
///
/// let mut expr = quot().app(6.into()).app(2.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 3.into());
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

// TODO: find an independent variant, like with quot()
/// Applied to two Church-encoded numbers it returns a Church-encoded remainder of their division.
///
/// REM := λab. SECOND (DIV a b) = λ λ SECOND (DIV 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::rem;
///
/// let mut expr = rem().app(3.into()).app(2.into());
/// expr.beta_full();
///
/// assert_eq!(expr, 1.into());
/// ```
pub fn rem() -> Term {
    abs(abs(
        second().app(
            div()
            .app(Var(2))
            .app(Var(1))
        )
    ))
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
    use reduction::beta_full;
    use combinators::c;

    #[test]
    fn church_invalid_nums() {
        assert_eq!(tru().is_cnum(),       false);
        assert_eq!(Var(1).is_cnum(),      false);
        assert_eq!(abs(Var(1)).is_cnum(), false);
    }

    #[test]
    fn church_number_values() {
        for n in 0..10 { assert_eq!(Term::from(n).value(), Ok(n)) }
    }

    #[test]
    fn church_successor() {
        assert_eq!(beta_full(succ().app(0.into())), 1.into());
        assert_eq!(beta_full(succ().app(1.into())), 2.into());
        assert_eq!(beta_full(succ().app(2.into())), 3.into());
    }

    #[test]
    fn church_predecessor() {
        assert_eq!(beta_full(pred().app(0.into())), 0.into());
        assert_eq!(beta_full(pred().app(1.into())), 0.into());
        assert_eq!(beta_full(pred().app(5.into())), 4.into());
    }

    #[test]
    fn church_plus_sub_equivalents() {
        assert_eq!(beta_full(plus().app(1.into())), succ()); // PLUS 1 → SUCC
        assert_eq!(beta_full(c().app(sub()).app(1.into())), pred()); // C SUB 1 → PRED
    }

    #[test]
    fn church_multiplication() {
        assert_eq!(beta_full(mult().app(3.into()).app(4.into())), 12.into());
        assert_eq!(beta_full(mult().app(1.into()).app(3.into())), 3.into());
        assert_eq!(beta_full(mult().app(3.into()).app(1.into())), 3.into());
        assert_eq!(beta_full(mult().app(5.into()).app(0.into())), 0.into());
        assert_eq!(beta_full(mult().app(0.into()).app(5.into())), 0.into());
    }

    #[test]
    fn church_exponentiation() {
        assert_eq!(beta_full(pow().app(2.into()).app(4.into())), 16.into());
        assert_eq!(beta_full(pow().app(1.into()).app(3.into())), 1.into());
        assert_eq!(beta_full(pow().app(3.into()).app(1.into())), 3.into());
        assert_eq!(beta_full(pow().app(5.into()).app(0.into())), 1.into());
        assert_eq!(beta_full(pow().app(0.into()).app(5.into())), 0.into());
    }
    
    #[test]
    fn church_division() {
        assert_eq!(beta_full(div().app(2.into()).app(2.into())), (1.into(), 0.into()).into());
        assert_eq!(beta_full(div().app(3.into()).app(2.into())), (1.into(), 1.into()).into());
        assert_eq!(beta_full(div().app(2.into()).app(1.into())), (2.into(), 0.into()).into());
        assert_eq!(beta_full(div().app(0.into()).app(3.into())), (0.into(), 0.into()).into());
        // assert_eq!(beta_full(div().app(1.into()).app(0.into())), ); division by 0 hangs
    }
    
    #[test]
    fn church_quotient() {
        assert_eq!(beta_full(quot().app(2.into()).app(2.into())), 1.into());
        assert_eq!(beta_full(quot().app(3.into()).app(2.into())), 1.into());
        assert_eq!(beta_full(quot().app(2.into()).app(1.into())), 2.into());
        assert_eq!(beta_full(quot().app(0.into()).app(3.into())), 0.into());
        // assert_eq!(beta_full(quot().app(1.into()).app(0.into())), ); division by 0 hangs
    }
    
    #[test]
    fn church_remainder() {
        assert_eq!(beta_full(rem().app(2.into()).app(2.into())), 0.into());
        assert_eq!(beta_full(rem().app(3.into()).app(2.into())), 1.into());
        assert_eq!(beta_full(rem().app(2.into()).app(1.into())), 0.into());
        assert_eq!(beta_full(rem().app(0.into()).app(3.into())), 0.into());
        // assert_eq!(beta_full(quot().app(1.into()).app(0.into())), ); division by 0 hangs
    }
}
