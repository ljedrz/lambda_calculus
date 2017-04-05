use term::*;
use term::Term::*;

// TRUE := λxy.x
pub fn tru() -> Term { abs(abs(Var(2))) }

// FALSE := λxy.y
pub fn fls() -> Term { abs(abs(Var(1))) }

// AND := λpq.p q p
pub fn and() -> Term { abs(abs(Var(2).app(Var(1)).app(Var(2)))) }

// OR := λpq.p p q
pub fn or() -> Term { abs(abs(Var(2).app(Var(2)).app(Var(1)))) }

// NOT := λp.p FALSE TRUE
pub fn not() -> Term { abs(Var(1).app(fls()).app(tru())) }

// XOR := λpab.p a b
pub fn xor() -> Term { abs(abs(Var(2).app(not().app(Var(1))).app(Var(1)))) }

// IFELSE := λpab.p a b
pub fn if_else() -> Term { abs(abs(abs(Var(3).app(Var(2)).app(Var(1))))) }

#[cfg(test)]
mod test {
	use super::*;
	use reduction::*;
	use arithmetic::*;

	#[test]
	fn chuch_and() {
		let and_true_true	= and().app(tru()).app(tru());
		let and_true_false	= and().app(tru()).app(fls());
		let and_false_true	= and().app(fls()).app(tru());
		let and_false_false = and().app(fls()).app(fls());

		assert_eq!(normalize(and_true_true), tru());
		assert_eq!(normalize(and_true_false), fls());
		assert_eq!(normalize(and_false_true), fls());
		assert_eq!(normalize(and_false_false), fls());
	}

	#[test]
	fn chuch_or() {
		let or_true_true   = or().app(tru()).app(tru());
		let or_true_false  = or().app(tru()).app(fls());
		let or_false_true  = or().app(fls()).app(tru());
		let or_false_false = or().app(fls()).app(fls());

		assert_eq!(normalize(or_true_true), tru());
		assert_eq!(normalize(or_true_false), tru());
		assert_eq!(normalize(or_false_true), tru());
		assert_eq!(normalize(or_false_false), fls());
	}

	#[test]
	fn chuch_not() {
		let not_true  = not().app(tru());
		let not_false = not().app(fls());

		assert_eq!(normalize(not_true), fls());
		assert_eq!(normalize(not_false), tru());
	}

	#[test]
	fn chuch_xor() {
		let xor_true_true   = xor().app(tru()).app(tru());
		let xor_true_false  = xor().app(tru()).app(fls());
		let xor_false_true  = xor().app(fls()).app(tru());
		let xor_false_false = xor().app(fls()).app(fls());

		assert_eq!(normalize(xor_true_true), fls());
		assert_eq!(normalize(xor_true_false), tru());
		assert_eq!(normalize(xor_false_true), tru());
		assert_eq!(normalize(xor_false_false), fls());
	}

	#[test]
	fn church_if_else() {
		let if_true_one_else_zero  = if_else().app(tru()).app(one()).app(zero());
		let if_false_one_else_zero = if_else().app(fls()).app(one()).app(zero());

		assert_eq!(normalize(if_true_one_else_zero), one());
		assert_eq!(normalize(if_false_one_else_zero), zero());
	}
}