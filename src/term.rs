use self::Term::*;
use self::Error::*;

/// A lambda term that is either a variable with a De Bruijn index, an abstraction over a term or
/// an applicaction of one term to another.
#[derive(Debug, PartialEq, Clone)]
pub enum Term {
	Var(usize),
	Abs(Box<Term>),
	App(Box<Term>, Box<Term>)
}

/// An error that can be returned when an inapplicable function is applied to a term.
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
	/// Applies self to another term
	pub fn app(self, argument: Term) -> Term { App(Box::new(self), Box::new(argument)) }

	/// Consumes a lambda variable and returns its De Bruijn index.
	pub fn unvar(self) -> Result<usize, Error> {
		match self {
			Var(n) => Ok(n),
			_ => Err(NotAVar)
		}
	}

	/// Consumes an abstraction and returns its underlying term.
	pub fn unabs(self) -> Result<Term, Error> {
		match self {
			Abs(x) => Ok(*x),
			_ => Err(NotAnAbs)
		}
	}

	/// Returns a reference to an abstraction's underlying term.
	pub fn unabs_ref(&self) -> Result<&Term, Error> {
		match *self {
			Abs(ref x) => Ok(&*x),
			_ => Err(NotAnAbs)
		}
	}

	/// Returns a mutable reference to an abstraction's underlying term.
	pub fn unabs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		match *self {
			Abs(ref mut x) => Ok(&mut *x),
			_ => Err(NotAnAbs)
		}
	}

	/// Consumes an application and returns a pair containing its underlying terms.
	pub fn unapp(self) -> Result<(Term, Term), Error> {
		match self {
			App(lhs, rhs) => Ok((*lhs, *rhs)),
			_ => Err(NotAnApp)
		}
	}

	/// Returns a pair containing references to an application's underlying terms.
	pub fn unapp_ref(&self) -> Result<(&Term, &Term), Error> {
		match *self {
			App(ref lhs, ref rhs) => Ok((&*lhs, &*rhs)),
			_ => Err(NotAnApp)
		}
	}

	/// Returns a pair containing mutable references to an application's underlying terms.
	pub fn unapp_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
		match *self {
			App(ref mut lhs, ref mut rhs) => Ok((&mut *lhs, &mut *rhs)),
			_ => Err(NotAnApp)
		}
	}

	/// Returns the left-hand side term of an application. Consumes its argument.
	pub fn lhs(self) -> Result<Term, Error> {
		if let Ok((lhs, _)) = self.unapp() { Ok(lhs) } else { Err(NotAnApp) }
	}

	/// Returns a reference to the left-hand side term of an application.
	pub fn lhs_ref(&self) -> Result<&Term, Error> {
		if let Ok((lhs, _)) = self.unapp_ref() { Ok(lhs) } else { Err(NotAnApp) }
	}

	/// Returns a mutable reference to the left-hand side term of an application.
	pub fn lhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		if let Ok((lhs, _)) = self.unapp_ref_mut() { Ok(lhs) } else { Err(NotAnApp) }
	}

	/// Returns the right-hand side term of an application. Consumes its argument.
	pub fn rhs(self) -> Result<Term, Error> {
		if let Ok((_, rhs)) = self.unapp() { Ok(rhs) } else { Err(NotAnApp) }
	}

	/// Returns a reference to the right-hand side term of an application.
	pub fn rhs_ref(&self) -> Result<&Term, Error> {
		if let Ok((_, rhs)) = self.unapp_ref() { Ok(rhs) } else { Err(NotAnApp) }
	}

	/// Returns a mutable reference to the right-hand side term of an application.
	pub fn rhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
		if let Ok((_, rhs)) = self.unapp_ref_mut() { Ok(rhs) } else { Err(NotAnApp) }
	}
}

/// Wraps a term in an abstraction. Consumes its argument.
pub fn abs(term: Term) -> Term { Abs(Box::new(term)) }

/// Produces an application of its arguments, consuming them in the process.
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new(lhs), Box::new(rhs)) }