use self::Term::*;
use self::Error::*;

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
	Var(usize),
	Abs(Box<Term>),
	App(Box<Term>, Box<Term>)
}

#[derive(Debug, PartialEq, Clone)]
pub enum Error {
	NotAVar,
	NotAnAbs,
	NotAnApp,
	NotANum,
	NotAPair,
	NotAList
}

impl Term {
	pub fn app(self, term: Term) -> Term { App(Box::new(self), Box::new(term)) }

	pub fn unvar(self) -> Result<usize, Error> {
		match self {
			Var(n) => Ok(n),
			_ => Err(NotAVar)
		}
	}

	pub fn unabs(self) -> Result<Term, Error> {
		match self {
			Abs(x) => Ok(*x),
			_ => Err(NotAnAbs)
		}
	}

	pub fn unabs_ref(&self) -> Result<&Term, Error> {
		match *self {
			Abs(ref x) => Ok(&*x),
			_ => Err(NotAnAbs)
		}
	}

	pub fn unabs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		match *self {
			Abs(ref mut x) => Ok(&mut *x),
			_ => Err(NotAnAbs)
		}
	}

	pub fn unapp(self) -> Result<(Term, Term), Error> {
		match self {
			App(lhs, rhs) => Ok((*lhs, *rhs)),
			_ => Err(NotAnApp)
		}
	}

	pub fn unapp_ref(&self) -> Result<(&Term, &Term), Error> {
		match *self {
			App(ref lhs, ref rhs) => Ok((&*lhs, &*rhs)),
			_ => Err(NotAnApp)
		}
	}

	pub fn unapp_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
		match *self {
			App(ref mut lhs, ref mut rhs) => Ok((&mut *lhs, &mut *rhs)),
			_ => Err(NotAnApp)
		}
	}

	pub fn lhs(self) -> Result<Term, Error> {
		if let Ok((lhs, _)) = self.unapp() { Ok(lhs) } else { Err(NotAnApp) }
	}

	pub fn lhs_ref(&self) -> Result<&Term, Error> {
		if let Ok((lhs, _)) = self.unapp_ref() { Ok(lhs) } else { Err(NotAnApp) }
	}

	pub fn lhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		if let Ok((lhs, _)) = self.unapp_ref_mut() { Ok(lhs) } else { Err(NotAnApp) }
	}

	pub fn rhs(self) -> Result<Term, Error> {
		if let Ok((_, rhs)) = self.unapp() { Ok(rhs) } else { Err(NotAnApp) }
	}

	pub fn rhs_ref(&self) -> Result<&Term, Error> {
		if let Ok((_, rhs)) = self.unapp_ref() { Ok(rhs) } else { Err(NotAnApp) }
	}

	pub fn rhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		if let Ok((_, rhs)) = self.unapp_ref_mut() { Ok(rhs) } else { Err(NotAnApp) }
	}
}

pub fn abs(term: Term) -> Term { Abs(Box::new(term)) }
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new(lhs), Box::new(rhs)) }