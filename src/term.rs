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
    /// Applies self to another term.
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

    /// Returns the left-hand side term of an application. Consumes self.
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

    /// Returns the right-hand side term of an application. Consumes self.
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

/// Produces an application of its arguments, consuming them in the process.
///
/// # Example
/// ```
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::app;
///
/// assert_eq!(app(Var(0), Var(1)), App(Box::new(Var(0)), Box::new(Var(1))));
/// ```
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new(lhs), Box::new(rhs)) }

fn parenthesize_if(condition: bool, input: &str) -> Cow<str> {
    if condition {
        format!("({})", input).into()
    } else {
        input.into()
    }
}

/// Set to `true` for λ or `false` for \ when displaying lambda terms. The default is `true`.
pub const DISPLAY_PRETTY: bool = true;

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

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence(0, self))
    }
}

#[cfg(test)]
mod test {
    use arithmetic::*;

    #[test]
    fn displaying_terms() {
        assert_eq!(&format!("{}", zero()), "λλ1");
        assert_eq!(&format!("{}", succ()), "λλλ2(321)");
        assert_eq!(&format!("{}", pred()), "λλλ3(λλ1(24))(λ2)(λ1)");
    }
}
