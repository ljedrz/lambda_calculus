//! A `module` with a Church-encoded pair and related functions.

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;

/// Produces a Church-encoded pair; applying it to two other terms puts them inside it.
///
/// pair := λxyz.z x y = λ λ λ 1 3 2
///
/// # Example
/// ```
/// use lambda_calculus::pair::pair;
/// use lambda_calculus::arithmetic::{zero, one};
///
/// let pair_0_1 = pair().app(zero()).app(one());
///
/// assert_eq!(pair_0_1.fst_ref(), Ok(&zero()));
///	assert_eq!(pair_0_1.snd_ref(), Ok(&one()));
/// ```
pub fn pair() -> Term { abs(abs(abs(Var(1).app(Var(3)).app(Var(2))))) }

/// Applied to a Church-encoded pair (a, b) it yields a.
///
/// first := λp.p (λxy.x) = λ 1 (λ λ 2)
///
/// # Example
/// ```
/// use lambda_calculus::pair::{pair, first};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// let pair_0_1 = pair().app(zero()).app(one());
///
/// assert_eq!(normalize(first().app(pair_0_1)), zero());
/// ```
pub fn first() -> Term { abs(Var(1).app(tru())) }

/// Applied to a Church-encoded pair (a, b) it yields b.
///
/// second := λp.p (λxy.y) = λ 1 (λ λ 1)
///
/// # Example
/// ```
/// use lambda_calculus::pair::{pair, second};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// let pair_0_1 = pair().app(zero()).app(one());
///
/// assert_eq!(normalize(second().app(pair_0_1)), one());
/// ```
pub fn second() -> Term { abs(Var(1).app(fls())) }

impl Term {
	/// Checks whether self is a Church-encoded pair.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert!(pair01.is_pair());
	/// ```
	pub fn is_pair(&self) -> bool {
		self.fst_ref().is_ok() && self.snd_ref().is_ok()
	}

	/// Splits a Church-encoded pair into a pair of terms, consuming self.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.unpair(), Ok((zero(), one())));
	/// ```
	pub fn unpair(self) -> Result<(Term, Term), Error> {
		if let Abs(_) = self {
			if let Ok((wrapped_a, b)) = self.unabs().and_then(|t| t.unapp()) {
				Ok((try!(wrapped_a.rhs()), b))
			} else {
				Err(NotAPair)
			}
		} else {
			if let Ok((wrapped_a, b)) = self.unapp() {
				Ok((try!(wrapped_a.rhs()), b))
			} else {
				Err(NotAPair)
			}
		}
	}

	/// Splits a Church-encoded pair into a pair of references to its underlying terms.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.unpair_ref(), Ok((&zero(), &one())));
	/// ```
	pub fn unpair_ref(&self) -> Result<(&Term, &Term), Error> {
		if let Abs(_) = *self {
			if let Ok((wrapped_a, b)) = self.unabs_ref().and_then(|t| t.unapp_ref()) {
				Ok((try!(wrapped_a.rhs_ref()), b))
			} else {
				Err(NotAPair)
			}
		} else {
			if let Ok((wrapped_a, b)) = self.unapp_ref() {
				Ok((try!(wrapped_a.rhs_ref()), b))
			} else {
				Err(NotAPair)
			}
		}
	}

	/// Splits a Church-encoded pair into a pair of mutable references to its underlying terms.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let mut pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.unpair_ref_mut(), Ok((&mut zero(), &mut one())));
	/// ```
	pub fn unpair_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
		if let Abs(_) = *self {
			if let Ok((wrapped_a, b)) = self.unabs_ref_mut().and_then(|t| t.unapp_ref_mut()) {
				Ok((try!(wrapped_a.rhs_ref_mut()), b))
			} else {
				Err(NotAPair)
			}
		} else {
			if let Ok((wrapped_a, b)) = self.unapp_ref_mut() {
				Ok((try!(wrapped_a.rhs_ref_mut()), b))
			} else {
				Err(NotAPair)
			}
		}
	}

	/// Returns the first term from a Church-encoded pair, consuming self.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.fst(), Ok(zero()));
	/// ```
	pub fn fst(self) -> Result<Term, Error> {
		Ok(try!(self.unpair()).0)
	}

	/// Returns a reference to the first term of a Church-encoded pair.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.fst_ref(), Ok(&zero()));
	/// ```
	pub fn fst_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.unpair_ref()).0)
	}

	/// Returns a mutable reference to the first term of a Church-encoded pair.
	/// Returns a reference to the first term of a Church-encoded pair.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let mut pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.fst_ref_mut(), Ok(&mut zero()));
	/// ```
	pub fn fst_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.unpair_ref_mut()).0)
	}

	/// Returns the second term from a Church-encoded pair, consuming self.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.snd(), Ok(one()));
	/// ```
	pub fn snd(self) -> Result<Term, Error> {
		Ok(try!(self.unpair()).1)
	}

	/// Returns a reference to the second term of a Church-encoded pair.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.snd_ref(), Ok(&one()));
	/// ```
	pub fn snd_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.unpair_ref()).1)
	}

	/// Returns a mutable reference to the second term of a Church-encoded pair.
	///
	/// # Example
	/// ```
	/// use lambda_calculus::pair::pair;
	/// use lambda_calculus::arithmetic::{zero, one};
	///
	/// let mut pair01 = pair().app(zero()).app(one());
	///
	/// assert_eq!(pair01.snd_ref_mut(), Ok(&mut one()));
	/// ```
	pub fn snd_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.unpair_ref_mut()).1)
	}
}


#[cfg(test)]
mod test {
	use super::*;
	use arithmetic::*;
	use reduction::*;

	#[test]
	fn pair_operations() {
		let pair_four_three = normalize(pair().app(to_cnum(4)).app(to_cnum(3)));

		assert!(pair_four_three.is_pair());

		assert_eq!(pair_four_three.fst_ref(), Ok(&to_cnum(4)));
		assert_eq!(pair_four_three.snd_ref(), Ok(&to_cnum(3)));

		let unpaired = pair_four_three.unpair();
		assert_eq!(unpaired, Ok((to_cnum(4), to_cnum(3))));
	}
}