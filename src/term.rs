//! [Lambda terms](https://en.wikipedia.org/wiki/Lambda_calculus#Lambda_terms)

pub use self::Term::*;
pub use self::Notation::*;
use self::Error::*;
use std::fmt;
use std::borrow::Cow;
use std::char::from_u32;

/// Set to `true` for λ or `false` for \ when displaying lambda terms. The default is `true`.
pub const PRETTY_LAMBDA: bool = true;

/// The notation used for parsing and displaying purposes.
///
/// # Example
/// ```
/// use lambda_calculus::term::Notation::*;
/// use lambda_calculus::arithmetic::succ;
///
/// assert_eq!(&format!(  "{}", succ()), "λa.λb.λc.b (a b c)");
/// assert_eq!(&format!("{:?}", succ()), "λλλ2(321)");
/// ```
#[derive(Debug, PartialEq)]
pub enum Notation {
    /// classic lambda calculus notation; the default `fmt::Display` mode
    Classic,
    /// De Bruijn indices; the `fmt::Debug` display mode
    DeBruijn
}

/// A lambda term that is either a variable with a De Bruijn index, an abstraction over a term or
/// an applicaction of one term to another.
#[derive(PartialEq, Clone)]
pub enum Term {
    /// a variable
    Var(usize),
    /// an abstraction
    Abs(Box<Term>),
    /// an application
    App(Box<Term>, Box<Term>)
}

/// An error that can be returned when an inapplicable function is applied to a term.
#[derive(Debug, PartialEq)]
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
            Var(ref n) => Ok(n),
            _ => Err(NotAVar)
        }
    }

    /// Returns a mutable reference to a variable's index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).unvar_ref_mut(), Ok(&mut 1));
    /// ```
    pub fn unvar_ref_mut(&mut self) -> Result<&mut usize, Error> {
        match *self {
            Var(ref mut n) => Ok(n),
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
            Abs(ref x) => Ok(x),
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
            Abs(ref mut x) => Ok(x),
            _ => Err(NotAnAbs)
        }
    }

    /// Consumes an application and returns a pair containing its underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).app(Var(2)).unapp(), Ok((Var(1), Var(2))));
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
    /// assert_eq!(Var(1).app(Var(2)).unapp_ref(), Ok((&Var(1), &Var(2))));
    /// ```
    pub fn unapp_ref(&self) -> Result<(&Term, &Term), Error> {
        match *self {
            App(ref lhs, ref rhs) => Ok((lhs, rhs)),
            _ => Err(NotAnApp)
        }
    }

    /// Returns a pair containing mutable references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).app(Var(2)).unapp_ref_mut(), Ok((&mut Var(1), &mut Var(2))));
    /// ```
    pub fn unapp_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        match *self {
            App(ref mut lhs, ref mut rhs) => Ok((lhs, rhs)),
            _ => Err(NotAnApp)
        }
    }

    /// Returns the left-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term::*;
    ///
    /// assert_eq!(Var(1).app(Var(2)).lhs(), Ok(Var(1)));
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
    /// assert_eq!(Var(1).app(Var(2)).lhs_ref(), Ok(&Var(1)));
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
    /// assert_eq!(Var(1).app(Var(2)).lhs_ref_mut(), Ok(&mut Var(1)));
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
    /// assert_eq!(Var(1).app(Var(2)).rhs(), Ok(Var(2)));
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
    /// assert_eq!(Var(1).app(Var(2)).rhs_ref(), Ok(&Var(2)));
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
    /// assert_eq!(Var(1).app(Var(2)).rhs_ref_mut(), Ok(&mut Var(2)));
    /// ```
    pub fn rhs_ref_mut(&mut self) -> Result<&mut Term, Error> {
        if let Ok((_, rhs)) = self.unapp_ref_mut() { Ok(rhs) } else { Err(NotAnApp) }
    }
}

/// Wraps a `Term` in an `Abs`traction. Consumes its argument.
///
/// # Example
/// ```
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::abs;
///
/// assert_eq!(abs(Var(1)), Abs(Box::new(Var(1))));
/// ```
pub fn abs(term: Term) -> Term { Abs(Box::new(term)) }

/// Produces an `App`lication of 2 given `Term`s without any reduction, consuming them in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::app;
///
/// assert_eq!(app(Var(1), Var(2)), App(Box::new(Var(1)), Box::new(Var(2))));
/// ```
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new(lhs), Box::new(rhs)) }

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence_cla(self, 0, 0))
    }
}

#[doc(hidden)]
pub fn show_precedence_cla(term: &Term, context_precedence: usize, depth: u32) -> String {
    match *term {
        Var(i) => {
            if depth >= i as u32 {
                format!("{}", from_u32(depth + 97 - i as u32).expect("error while printing term"))
            } else {
                format!("{}", from_u32(96 + i as u32).expect("error while printing term"))
            }
        },
        Abs(ref t) => {
            let ret = {
                format!("{}{}.{}", if PRETTY_LAMBDA { 'λ' } else { '\\' },
                    from_u32(depth + 97).expect("error while printing term"),
                    show_precedence_cla(t, 0, depth + 1)
                )
            };
            parenthesize_if(&ret, context_precedence > 1).into()
        },
        App(ref t1, ref t2) => {
            let ret = format!("{} {}",
                show_precedence_cla(t1, 2, depth), show_precedence_cla(t2, 3, depth));
            parenthesize_if(&ret, context_precedence == 3).into()
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence_dbr(self, 0, 0))
    }
}

#[doc(hidden)]
pub fn show_precedence_dbr(term: &Term, context_precedence: usize, depth: u32) -> String {
    match *term {
        Var(i) => {
            format!("{:X}", i)
        },
        Abs(ref t) => {
            let ret = format!("{}{:?}", if PRETTY_LAMBDA { 'λ' } else { '\\' }, t);
            parenthesize_if(&ret, context_precedence > 1).into()
        },
        App(ref t1, ref t2) => {
            let ret = format!("{}{}",
                show_precedence_dbr(t1, 2, depth), show_precedence_dbr(t2, 3, depth));
            parenthesize_if(&ret, context_precedence == 3).into()
        }
    }
}

fn parenthesize_if(input: &str, condition: bool) -> Cow<str> {
    if condition {
        format!("({})", input).into()
    } else {
        input.into()
    }
}

/// A macro for chain application of `Term`s.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term::*;
/// use lambda_calculus::term::app;
///
/// assert_eq!(app!(Var(1), Var(2), Var(3)), Var(1).app(Var(2)).app(Var(3)));
/// # }
/// ```
#[macro_export]
macro_rules! app {
    ($term1:expr, $($term2:expr),+) => {
        {
            let mut term = $term1;
            $(term = term.app($term2);)*
            term
        }
    };
}

#[cfg(test)]
mod tests {
    use super::{Var, PRETTY_LAMBDA};
    use super::Notation::DeBruijn;
    use parser::parse;
    use arithmetic::{zero, succ, pred};

    #[test]
    fn app_macro() {
        assert_eq!(app!(succ(), app!(Var(1), Var(2), Var(3))),
                   succ().app(Var(1).app(Var(2)).app(Var(3)))
        );
    }

    #[test]
    fn open_term_display() {
        assert_eq!(&format!("{}", parse("λ2",  DeBruijn).unwrap()), "λa.b");
        assert_eq!(&format!("{}", parse("λ3",  DeBruijn).unwrap()), "λa.c");
        assert_eq!(&format!("{}", parse("λλ3", DeBruijn).unwrap()), "λa.λb.c");
        assert_eq!(&format!("{}", parse("λλ4", DeBruijn).unwrap()), "λa.λb.d");
    }

    #[test]
    fn display_modes() {
        if PRETTY_LAMBDA {
            assert_eq!(&format!("{}", zero()), "λa.λb.b");
            assert_eq!(&format!("{}", succ()), "λa.λb.λc.b (a b c)");
            assert_eq!(&format!("{}", pred()), "λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)");

            assert_eq!(&format!("{:?}", zero()), "λλ1");
            assert_eq!(&format!("{:?}", succ()), "λλλ2(321)");
            assert_eq!(&format!("{:?}", pred()), "λλλ3(λλ1(24))(λ2)(λ1)");
        } else {
            assert_eq!(&format!("{}", zero()), r#"\a.\b.b"#);
            assert_eq!(&format!("{}", succ()), r#"\a.\b.\c.b (a b c)"#);
            assert_eq!(&format!("{}", pred()), r#"\a.\b.\c.a (\d.\e.e (d b)) (\d.c) (\d.d)"#);

            assert_eq!(&format!("{:?}", zero()), r#"\\1"#);
            assert_eq!(&format!("{:?}", succ()), r#"\\\2(321)"#);
            assert_eq!(&format!("{:?}", pred()), r#"\\\3(\\1(24))(\2)(\1)"#);
        }
    }
}
