use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;
use reduction::*;

// PAIR := λxyf.f x y
pub fn pair() -> Term { abs(abs(abs(Var(1).app(Var(3)).app(Var(2))))) }

// FIRST := λp.p TRUE
pub fn first() -> Term { abs(Var(1).app(tru())) }

// SECOND := λp.p FALSE
pub fn second() -> Term { abs(Var(1).app(fls())) }

// NIL := λx.TRUE
pub fn nil() -> Term { abs(tru()) }

// NULL := λp.p (λxy.FALSE)
pub fn null() -> Term { abs(Var(1).app(abs(abs(fls())))) }

// CONS := λht.PAIR FALSE (PAIR h t)
pub fn cons() -> Term { abs(abs(pair().app(fls()).app(pair().app(Var(2)).app(Var(1))))) }

// HEAD := λz.FIRST (SECOND z)
pub fn head() -> Term { abs(first().app(second().app(Var(1)))) }

// TAIL := λz.SECOND (SECOND z)
pub fn tail() -> Term { abs(second().app(second().app(Var(1)))) }

impl Term {
	pub fn is_pair(&self) -> bool {
		self.fst_ref().is_ok() && self.snd_ref().is_ok()
	}

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

	pub fn fst(self) -> Result<Term, Error> {
		Ok(try!(self.unpair()).0)
	}

	pub fn fst_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.unpair_ref()).0)
	}

	pub fn fst_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.unpair_ref_mut()).0)
	}

	pub fn snd(self) -> Result<Term, Error> {
		Ok(try!(self.unpair()).1)
	}

	pub fn snd_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.unpair_ref()).1)
	}

	pub fn snd_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.unpair_ref_mut()).1)
	}

	pub fn last_ref(&self) -> Result<&Term, Error> {
		let mut last_candidate = try!(self.snd_ref());

		while let Ok(ref second) = last_candidate.snd_ref() {
			last_candidate = *second;
		}

		Ok(last_candidate)
	}

	pub fn is_nil(&self) -> bool {
		*self == nil()
	}

	pub fn is_list(&self) -> bool {
		self.is_pair() && self.last_ref() == Ok(&nil())
	}

	pub fn uncons(self) -> Result<(Term, Term), Error> {
		if !self.is_list() {
			Err(NotAList)
		} else {
			self.unabs()
				.and_then(|t| t.snd())
				.and_then(|t| t.unpair())
		}
	}

	pub fn uncons_ref(&self) -> Result<(&Term, &Term), Error> {
		if !self.is_list() {
			Err(NotAList)
		} else {
			self.unabs_ref()
				.and_then(|t| t.snd_ref())
				.and_then(|t| t.unpair_ref())
		}
	}

	pub fn uncons_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
		if !self.is_list() {
			Err(NotAList)
		} else {
			self.unabs_ref_mut()
				.and_then(|t| t.snd_ref_mut())
				.and_then(|t| t.unpair_ref_mut())
		}
	}

	pub fn head(self) -> Result<Term, Error> {
		Ok(try!(self.uncons()).0)
	}

	pub fn head_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.uncons_ref()).0)
	}

	pub fn head_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.uncons_ref_mut()).0)
	}

	pub fn tail(self) -> Result<Term, Error> {
		Ok(try!(self.uncons()).1)
	}

	pub fn tail_ref(&self) -> Result<&Term, Error> {
		Ok(try!(self.uncons_ref()).1)
	}

	pub fn tail_ref_mut(&mut self) -> Result<&mut Term, Error> {
		Ok(try!(self.uncons_ref_mut()).1)
	}

	pub fn len(&self) -> Result<usize, Error> {
		let mut inner = self;
		let mut n = 0;

		while *inner != nil() {
			n += 1;
			inner = try!(inner.tail_ref());
		}

		Ok(n)
	}

	pub fn push(self, t: Term) -> Term {
		normalize(cons().app(t).app(self))
	}

	pub fn pop(&mut self) -> Result<Term, Error> {
		let (head, tail) = try!(self.clone().uncons());
		*self = tail;

		Ok(head)
	}
}

impl From<Vec<Term>> for Term {
	fn from(terms: Vec<Term>) -> Self {
		let mut output = nil();

		for t in terms.into_iter().rev() {
			output = cons().app(t).app(output);
		}

		normalize(output)
	}
}

impl Iterator for Term {
	type Item = Term;

	fn next(&mut self) -> Option<Term> {
		if self.is_nil() {
			None
		} else {
			Some(self.pop().unwrap())
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use arithmetic::*;

	#[test]
	fn pair_operations() {
		let pair_four_three = normalize(pair().app(to_cnum(4)).app(to_cnum(3)));

		assert!(pair_four_three.is_pair());

		assert_eq!(pair_four_three.fst_ref(), Ok(&to_cnum(4)));
		assert_eq!(pair_four_three.snd_ref(), Ok(&to_cnum(3)));

		let unpaired = pair_four_three.unpair();
		assert_eq!(unpaired, Ok((to_cnum(4), to_cnum(3))));
	}

	#[test]
	fn empty_list() {
		let nil = nil();

		assert!(nil.is_nil());
		assert!(!nil.is_list());
		assert_eq!(nil.uncons(), Err(NotAList));
	}

	#[test]
	fn list_push() {
		let list_pushed = nil().push(zero()).push(one()).push(one());
		let list_manual = normalize(cons().app(one()).app(cons().app(one()).app(cons().app(zero()).app(nil()))));

		assert_eq!(list_pushed, list_manual);
	}

	#[test]
	fn list_from_vector() {
		let list_from_vec = Term::from(vec![one(), one(), zero()]);
		let list_pushed = nil().push(zero()).push(one()).push(one());

		assert_eq!(list_from_vec, list_pushed);
	}

	#[test]
	fn list_length() {
		let list0 = nil();
		assert_eq!(list0.len(), Ok(0));
		let list1 = list0.push(one());
		assert_eq!(list1.len(), Ok(1));
		let list2 = list1.push(one());
		assert_eq!(list2.len(), Ok(2));
		let list3 = list2.push(one());
		assert_eq!(list3.len(), Ok(3));
	}

	#[test]
	fn list_operations() {
		let list_three_five_four = Term::from(vec![to_cnum(3), to_cnum(5), to_cnum(4)]);

		assert!(list_three_five_four.is_list());

		assert_eq!(list_three_five_four.head_ref(), Ok(&to_cnum(3)));
		assert_eq!(list_three_five_four.tail_ref(), Ok(&Term::from(vec![to_cnum(5), to_cnum(4)])));

		assert_eq!(list_three_five_four.tail_ref().and_then(|t| t.head_ref()), Ok(&to_cnum(5)));
		assert_eq!(list_three_five_four.tail_ref().and_then(|t| t.tail_ref()).and_then(|t| t.head_ref()), Ok(&to_cnum(4)));

		let unconsed = list_three_five_four.uncons();
		assert_eq!(unconsed, Ok((to_cnum(3), Term::from(vec![to_cnum(5), to_cnum(4)]))));
	}


	#[test]
	fn list_pop() {
		let mut list_poppable = Term::from(vec![one(), zero(), zero()]);

		assert_eq!(list_poppable.pop(), Ok(one()));
		assert_eq!(list_poppable.pop(), Ok(zero()));
		assert_eq!(list_poppable.pop(), Ok(zero()));
		assert_eq!(list_poppable.pop(), Err(NotAList));
	}

	#[test]
	fn iterating_list() {
		let list010 = Term::from(vec![zero(), one(), zero()]);
		let mut iter = list010.into_iter();

		assert_eq!(iter.next(), Some(zero()));
		assert_eq!(iter.next(), Some(one()));
		assert_eq!(iter.next(), Some(zero()));
		assert_eq!(iter.next(), None);
	}

}