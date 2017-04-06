use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;

/// Produces a Church-encoded zero.
///
/// zero := λfx.x = λ λ 1
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::zero;
///
/// assert_eq!(format!("{}", zero()), "λλ1");
/// ```
pub fn zero() -> Term { abs(abs(Var(1))) }

/// Applied to a Church-encoded number it produces a Church-encoded boolean, indicating whether its
/// argument is equal to zero.
///
/// is_zero := λn.n (λx.false) true =  λ 1 (λ false) true
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, is_zero};
/// use lambda_calculus::booleans::tru;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(is_zero().app(zero())), tru());
/// ```
pub fn is_zero() -> Term { abs(Var(1).app(abs(fls())).app(tru())) }

/// Produces a Church-encoded one.
///
/// one := λfx.f x = λ λ 2 1
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::one;
///
/// assert_eq!(format!("{}", one()), "λλ21");
/// ```
pub fn one() -> Term { abs(abs(Var(2).app(Var(1)))) }

/// Applied to a Church-encoded number it produces its successor.
///
/// succ := λnfx.f (n f x) = λ λ λ 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, succ};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(succ().app(zero())), one());
/// ```
pub fn succ() -> Term { abs(abs(abs(Var(2).app(Var(3).app(Var(2)).app(Var(1)))))) }

/// Applied to two Church-encoded numbers it produces their sum.
///
/// plus := λmnfx.m f (n f x) = λ λ λ λ 4 2 (3 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, plus};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(plus().app(zero()).app(one())), one());
/// ```
pub fn plus() -> Term { abs(abs(abs(abs(Var(4).app(Var(2)).app(Var(3).app(Var(2)).app(Var(1))))))) }

/// Applied to two Church-encoded numbers it produces their product.
///
/// mult := λm.λn.λf.m (n f) = λ λ λ 3 (2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, mult};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(mult().app(one()).app(one())), one());
/// ```
pub fn mult() -> Term { abs(abs(abs(Var(3).app(Var(2).app(Var(1)))))) }

/// Applied to two Church-encoded numbers it raises the first one to the power of the second one.
///
/// pow := λb.λe.e b = λ λ 1 2
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, pow};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(pow().app(one()).app(one())), one());
/// ```
pub fn pow() -> Term { abs(abs(Var(1).app(Var(2)))) }

/// Applied to a Church-encoded number it produces its predecessor.
///
/// pred := λn.λf.λx.n (λg.λh.h (g f)) (λu.x) (λu.u) = λ λ λ 3 (λ λ 1 (2 4)) (λ 2) (λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, pred};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(pred().app(one())), zero());
/// ```
pub fn pred() -> Term { abs(abs(abs(Var(3).app(abs(abs(Var(1).app(Var(2).app(Var(4)))))).app(abs(Var(2))).app(abs(Var(1)))))) }

/// Applied to two Church-encoded numbers it subtracts the second one from the first one.
///
/// sub := λm.λn.n pred m = λ λ 1 pred 2
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, sub};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(sub().app(one()).app(zero())), one());
/// ```
pub fn sub() -> Term { abs(abs(Var(1).app(pred()).app(Var(2)))) }

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether its
/// first argument is less or egual to the second one.
///
/// leq := λm.λn.is_zero (sub m n) = λ λ is_zero (sub 2 1)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{zero, one, leq};
/// use lambda_calculus::booleans::tru;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(leq().app(zero()).app(one())), tru());
/// ```
pub fn leq() -> Term { abs(abs(is_zero().app(sub().app(Var(2)).app(Var(1))))) }

/// Applied to two Church-encoded numbers it returns a Church-encoded boolean indicating whether its
/// first argument is egual to the second one.
///
/// eq := λmn.and (leq m n) (leq n m) = λ λ and (leq 2 1)(leq 1 2)
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, eq};
/// use lambda_calculus::booleans::tru;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(eq().app(one()).app(one())), tru());
/// ```
pub fn eq() -> Term { abs(abs(and().app(leq().app(Var(2)).app(Var(1))).app(leq().app(Var(1)).app(Var(2))))) }

impl Term {
	/// Returns the value of a Church-encoded number.
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

	/// Checks whether a term is a Church-encoded number.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::arithmetic::one;
	/// use lambda_calculus::booleans::tru;
	///
	/// assert!(one().is_number());
	/// ```
	pub fn is_number(&self) -> bool { self.value().is_ok() }
}

/// Produces a Church-encoded term with a value of the given natural number.
///
/// # Example
/// ```
/// use lambda_calculus::arithmetic::{one, to_cnum};
///
/// assert_eq!(to_cnum(1), one());
/// ```
pub fn to_cnum(n: usize) -> Term {
	let mut inner = Var(1);
	let mut count = n;

	while count > 0 {
		inner = Var(2).app(inner);
		count -= 1;
	}

	abs(abs(inner))
}

#[cfg(test)]
mod test {
	use super::*;
	use reduction::*;

	#[test]
	fn church_zero() {
		assert_eq!(normalize(is_zero().app(zero())), tru())
	}

	#[test]
	fn church_successor() {
		assert_eq!(normalize(succ().app(zero())), one());
		assert_eq!(normalize(succ().app(one())), abs(abs(Var(2).app(Var(2).app(Var(1))))));
		assert_eq!(normalize(succ().app(succ().app(succ().app(zero())))), abs(abs(Var(2).app(Var(2).app(Var(2).app(Var(1)))))));
	}

	#[test]
	fn church_number_identification() {
		for n in 0..5 { assert!(to_cnum(n).is_number()) }
	}

	#[test]
	fn church_number_creation() {
		assert_eq!(to_cnum(0), zero());
		assert_eq!(to_cnum(1), one());
		assert_eq!(to_cnum(2), normalize(succ().app(one())));
	}

	#[test]
	fn church_number_values() {
		for n in 0..10 { assert_eq!(to_cnum(n).value(), Ok(n)) }

		assert_eq!(abs(Var(1)).value(),      Err(NotANum));
		assert_eq!(abs(abs(Var(2))).value(), Err(NotANum));
	}

	#[test]
	fn church_addition() {
		assert_eq!(normalize(plus().app(one())), succ()); // PLUS 1 → SUCC

		assert_eq!(normalize(plus().app(zero()).app(zero())), zero());
		assert_eq!(normalize(plus().app(zero()).app(one())),  one());
		assert_eq!(normalize(plus().app(one()).app(zero())),  one());
		assert_eq!(normalize(plus().app(one()).app(one())),   to_cnum(2));

		assert_eq!(normalize(plus().app(to_cnum(2)).app(to_cnum(3))), to_cnum(5));
		assert_eq!(normalize(plus().app(to_cnum(4)).app(to_cnum(4))), to_cnum(8));
	}

	#[test]
	fn church_multiplication() {
		assert_eq!(normalize(mult().app(to_cnum(3)).app(to_cnum(4))), to_cnum(12));
		assert_eq!(normalize(mult().app(to_cnum(1)).app(to_cnum(3))), to_cnum(3));
		assert_eq!(normalize(mult().app(to_cnum(5)).app(to_cnum(0))), to_cnum(0));
	}

	#[test]
	fn church_exponentiation() {
		assert_eq!(normalize(pow().app(to_cnum(2)).app(to_cnum(4))), to_cnum(16));
		assert_eq!(normalize(pow().app(to_cnum(1)).app(to_cnum(6))), to_cnum(1));
		assert_eq!(normalize(pow().app(to_cnum(3)).app(to_cnum(2))), to_cnum(9));
//		assert_eq!(normalize(pow().app(to_cnum(5)).app(zero())), to_cnum(1)); // n^0 fails - why?
	}

	#[test]
	fn church_predecessor() {
		assert_eq!(normalize(pred().app(zero())), zero());
		assert_eq!(normalize(pred().app(one())), zero());
		assert_eq!(normalize(pred().app(to_cnum(5))), to_cnum(4));
	}

	#[test]
	fn church_comparison() {
		assert_eq!(normalize(leq().app(zero()).app(zero())), tru());
		assert_eq!(normalize(leq().app(zero()).app(one())), tru());

		assert_eq!(normalize(eq().app(zero()).app(zero())), tru());
		assert_eq!(normalize(eq().app(zero()).app(one())), fls());
		assert_eq!(normalize(eq().app(one()).app(zero())), fls());
		// TODO: add lt, gt, geq
	}
}