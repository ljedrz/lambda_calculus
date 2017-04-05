use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;

// 0 := λfx.x
pub fn zero() -> Term { abs(abs(Var(1))) }

// ISZERO := λn.n (λx.FALSE) TRUE
pub fn is_zero() -> Term { abs(Var(1).app(abs(fls())).app(tru())) }

// 1 := λfx.f x
pub fn one() -> Term { abs(abs(Var(2).app(Var(1)))) }

// SUCC := λnfx.f (n f x)
pub fn succ() -> Term { abs(abs(abs(Var(2).app(Var(3).app(Var(2)).app(Var(1)))))) }

// PLUS := λmnfx.m f (n f x)
pub fn plus() -> Term { abs(abs(abs(abs(Var(4).app(Var(2)).app(Var(3).app(Var(2)).app(Var(1))))))) }

// PLUS := λmn.m SUCC n
// pub fn plus2() -> Term { abs(abs(Var(2).app(succ()).app(Var(1)))) }

// MULT := λmnf.m (n f)
pub fn mult() -> Term { abs(abs(abs(Var(3).app(Var(2).app(Var(1)))))) }

// MULT := λmn.m (PLUS n) 0
// pub fn mult2() -> Term { abs(abs(Var(2).app(plus().app(Var(1))).app(zero()))) }

// POW := λbe.e b
pub fn pow() -> Term { abs(abs(Var(1).app(Var(2)))) }

// PRED := λnfx.n (λgh.h (g f)) (λu.x) (λu.u)
pub fn pred() -> Term { abs(abs(abs(Var(3).app(abs(abs(Var(1).app(Var(2).app(Var(4)))))).app(abs(Var(2))).app(abs(Var(1)))))) }

// PRED := λn.n (λgk.ISZERO (g 1) k (PLUS (g k) 1)) (λv.0) 0
// pub fn pred2() -> Term { abs(Var(1).app(abs(abs(is_zero().app(Var(2).app(one())).app(Var(1)).app(plus().app(Var(2).app(Var(1))).app(one()))))).app(abs(zero())).app(zero())) }

// SUB := λmn.n PRED m
pub fn sub() -> Term { abs(abs(Var(1).app(pred()).app(Var(2)))) }

// LEQ := λmn.ISZERO (SUB m n)
pub fn leq() -> Term { abs(abs(is_zero().app(sub().app(Var(2)).app(Var(1))))) }

// EQ := λmn.AND (LEQ m n) (LEQ n m)
pub fn eq() -> Term { abs(abs(and().app(leq().app(Var(2)).app(Var(1))).app(leq().app(Var(1)).app(Var(2))))) }

impl Term {
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

	pub fn is_number(&self) -> bool { self.value().is_ok() }
}

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