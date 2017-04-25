//! [Lambda terms](https://en.wikipedia.org/wiki/Lambda_calculus#Lambda_terms)

use self::Term::*;
use self::Error::*;
use std::fmt;
use std::borrow::Cow;

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
    /// Applies `self` to another term without substitution or reduction.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    /// use lambda_calculus::arithmetic::{zero, succ};
    ///
    /// assert_eq!(succ().app(zero()), App(Box::new(succ()), Box::new(zero())));
    /// ```
    pub fn app(self, argument: Term) -> Term { App(Box::new(self), Box::new(argument)) }

    /// Consumes a lambda variable and returns its De Bruijn index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).unvar(), Ok(1));
    /// ```
    pub fn unvar(self) -> Result<usize, Error> {
        match self {
            Var(n) => Ok(n),
            _ => Err(NotAVar)
        }
    }

    /// Returns a reference to a variable's index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).unvar_ref(), Ok(&1));
    /// ```
    pub fn unvar_ref(&self) -> Result<&usize, Error> {
        match *self {
            Var(ref n) => Ok(&n),
            _ => Err(NotAVar)
        }
    }

    /// Consumes an abstraction and returns its underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    /// use lambda_calculus::term::abs;
    ///
    /// assert_eq!(abs(Var(1)).unabs(), Ok(Var(1)));
    /// ```
    pub fn unabs(self) -> Result<Term, Error> {
        match self {
            Abs(x) => Ok(*x),
            _ => Err(NotAnAbs)
        }
    }

    /// Returns a reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    /// use lambda_calculus::term::abs;
    ///
    /// assert_eq!(abs(Var(1)).unabs_ref(), Ok(&Var(1)));
    /// ```
    pub fn unabs_ref(&self) -> Result<&Term, Error> {
        match *self {
            Abs(ref x) => Ok(&*x),
            _ => Err(NotAnAbs)
        }
    }

    /// Returns a mutable reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    /// use lambda_calculus::term::abs;
    ///
    /// assert_eq!(abs(Var(1)).unabs_ref_mut(), Ok(&mut Var(1)));
    /// ```
    pub fn unabs_ref_mut(&mut self) -> Result<&mut Term, Error> {
        match *self {
            Abs(ref mut x) => Ok(&mut *x),
            _ => Err(NotAnAbs)
        }
    }

    /// Consumes an application and returns a pair containing its underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).unapp(), Ok((Var(0), Var(1))));
    /// ```
    pub fn unapp(self) -> Result<(Term, Term), Error> {
        match self {
            App(lhs, rhs) => Ok((*lhs, *rhs)),
            _ => Err(NotAnApp)
        }
    }

    /// Returns a pair containing references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).unapp_ref(), Ok((&Var(0), &Var(1))));
    /// ```
    pub fn unapp_ref(&self) -> Result<(&Term, &Term), Error> {
        match *self {
            App(ref lhs, ref rhs) => Ok((&*lhs, &*rhs)),
            _ => Err(NotAnApp)
        }
    }

    /// Returns a pair containing mutable references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).unapp_ref_mut(), Ok((&mut Var(0), &mut Var(1))));
    /// ```
    pub fn unapp_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        match *self {
            App(ref mut lhs, ref mut rhs) => Ok((&mut *lhs, &mut *rhs)),
            _ => Err(NotAnApp)
        }
    }

    /// Returns the left-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).lhs(), Ok(Var(0)));
    /// ```
    pub fn lhs(self) -> Result<Term, Error> {
        if let Ok((lhs, _)) = self.unapp() { Ok(lhs) } else { Err(NotAnApp) }
    }

    /// Returns a reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).lhs_ref(), Ok(&Var(0)));
    /// ```
    pub fn lhs_ref(&self) -> Result<&Term, Error> {
        if let Ok((lhs, _)) = self.unapp_ref() { Ok(lhs) } else { Err(NotAnApp) }
    }

    /// Returns a mutable reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).lhs_ref_mut(), Ok(&mut Var(0)));
    /// ```
    pub fn lhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
        if let Ok((lhs, _)) = self.unapp_ref_mut() { Ok(lhs) } else { Err(NotAnApp) }
    }

    /// Returns the right-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).rhs(), Ok(Var(1)));
    /// ```
    pub fn rhs(self) -> Result<Term, Error> {
        if let Ok((_, rhs)) = self.unapp() { Ok(rhs) } else { Err(NotAnApp) }
    }

    /// Returns a reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).rhs_ref(), Ok(&Var(1)));
    /// ```
    pub fn rhs_ref(&self) -> Result<&Term, Error> {
        if let Ok((_, rhs)) = self.unapp_ref() { Ok(rhs) } else { Err(NotAnApp) }
    }

    /// Returns a mutable reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(0).app(Var(1)).rhs_ref_mut(), Ok(&mut Var(1)));
    /// ```
    pub fn rhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
        if let Ok((_, rhs)) = self.unapp_ref_mut() { Ok(rhs) } else { Err(NotAnApp) }
    }

    /// Applies `self` to another term with substitution and variable update, consuming them
    /// in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::parser::parse;
    ///
    /// let lhs    = parse(&"λλ42(λ13)").unwrap();
    /// let rhs    = parse(&"λ51").unwrap();
    /// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
    ///
    /// assert_eq!(lhs.apply(rhs), Ok(result));
    /// ```
    pub fn apply(self, rhs: Term) -> Result<Term, Error> {
        apply(self, rhs)
    }

    /// Reduces an `App`lication by substitution and variable update.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::{app, abs};
    /// use lambda_calculus::term::Term::Var;
    /// use lambda_calculus::arithmetic::zero;
    /// use lambda_calculus::combinators::i;
    ///
    /// assert_eq!(app(i(), zero()).eval(), Ok(abs(abs(Var(1)))));
    /// ```
    pub fn eval(self) -> Result<Term, Error> {
        let (lhs, rhs) = try!(self.unapp());

        apply(lhs, rhs)
    }
}

/// Wraps a term in an abstraction. Consumes its argument.
///
/// # Example
/// ```
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::abs;
///
/// assert_eq!(abs(Var(1)), Abs(Box::new(Var(1))));
/// ```
pub fn abs(term: Term) -> Term { Abs(Box::new(term)) }

/// Produces an application of its arguments without substitution or reduction, consuming them in
/// the process.
///
/// # Example
/// ```
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::app;
///
/// assert_eq!(app(Var(0), Var(1)), App(Box::new(Var(0)), Box::new(Var(1))));
/// ```
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new(lhs), Box::new(rhs)) }

/// Applies two terms with substitution and variable update, consuming them in the process.
///
/// # Example
/// ```
/// use lambda_calculus::term::apply;
/// use lambda_calculus::parser::parse;
///
/// let lhs    = parse(&"λλ42(λ13)").unwrap();
/// let rhs    = parse(&"λ51").unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
///
/// assert_eq!(apply(lhs, rhs), Ok(result));
/// ```
pub fn apply(mut lhs: Term, rhs: Term) -> Result<Term, Error> {
    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs; // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(_) => {
            _apply(lhs.unabs_ref_mut().unwrap(), rhs, depth + 1)
        },
        App(_, _) => {
            _apply(lhs.lhs_ref_mut().unwrap(), rhs.clone(), depth);
            _apply(lhs.rhs_ref_mut().unwrap(), rhs, depth)
        }
    }
}

fn update_free_variables(term: &mut Term, added_depth: usize, own_depth: usize) {
    match *term {
        Var(i) => if i > own_depth {
            *term = Var(i + added_depth)
        },
        Abs(_) => {
            update_free_variables(term.unabs_ref_mut().unwrap(), added_depth, own_depth + 1)
        },
        App(_, _) => {
            update_free_variables(term.lhs_ref_mut().unwrap(), added_depth, own_depth);
            update_free_variables(term.rhs_ref_mut().unwrap(), added_depth, own_depth)
        }
    }
}

/// Set to `true` for λ or `false` for \ when displaying lambda terms. The default is `true`.
pub const DISPLAY_PRETTY: bool = true;

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence(0, self))
    }
}

fn show_precedence(context_precedence: usize, term: &Term) -> String {
    match *term {
        Var(i) => format!("{:X}", i), // max. index = 15
        Abs(ref t) => {
            let ret = format!("{}{}", if DISPLAY_PRETTY { 'λ' } else { '\\' }, t);
            parenthesize_if(context_precedence > 1, &ret).into()
        },
        App(ref t1, ref t2) => {
            let ret = format!("{}{}", show_precedence(2, t1), show_precedence(3, t2));
            parenthesize_if(context_precedence == 3, &ret).into()
        }
    }
}

fn parenthesize_if(condition: bool, input: &str) -> Cow<str> {
    if condition {
        format!("({})", input).into()
    } else {
        input.into()
    }
}

#[cfg(test)]
mod test {
    use arithmetic::{zero, succ, pred};
    use combinators::i;
    use parser::parse;
    use super::{apply, abs};
    use super::Term::Var;

    #[test]
    fn applying() {
        let lhs    = parse(&"λλ42(λ13)").unwrap();
        let rhs    = parse(&"λ51").unwrap();
        let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
        assert_eq!(apply(lhs, rhs), Ok(result));

        assert_eq!(i().app(zero()).eval().unwrap(), abs(abs(Var(1))));
    }

    #[test]
    fn displaying_terms() {
        assert_eq!(&format!("{}", zero()), "λλ1");
        assert_eq!(&format!("{}", succ()), "λλλ2(321)");
        assert_eq!(&format!("{}", pred()), "λλλ3(λλ1(24))(λ2)(λ1)");
    }
}
