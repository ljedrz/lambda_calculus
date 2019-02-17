//! [Lambda terms](https://en.wikipedia.org/wiki/Lambda_calculus#Lambda_terms)

pub use self::Term::*;
pub use self::Notation::*;
use self::TermError::*;
use std::fmt;
use std::borrow::Cow;
use std::char::from_u32;

/// The character used to display lambda abstractions (a backslash).
#[cfg(feature = "backslash_lambda")]
pub const LAMBDA: char = '\\';

/// The character used to display lambda abstractions. The default is the Greek letter 'λ', but it
/// can also be set to a '\' (backslash) using `features = ["backslash_lambda"]`.
#[cfg(not(feature = "backslash_lambda"))]
pub const LAMBDA: char = 'λ';

/// An undefined term that can be used as a value returned by invalid/inapplicable operations, e.g.
/// obtaining an element of an empty list. Since this implementation uses De Bruijn indices greater
/// than zero, `Var(0)` will not occur naturally. It is displayed as `undefined`.
pub const UD: Term = Var(0);

/// The notation used for parsing and displaying purposes.
///
/// # Examples
/// ```
/// use lambda_calculus::combinators::S;
///
/// assert_eq!(&format!(  "{}", S()), "λa.λb.λc.a c (b c)"); // Classic notation
/// assert_eq!(&format!("{:?}", S()), "λλλ31(21)");          // DeBruijn index notation
/// ```
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Notation {
    /// classic lambda calculus notation; used by `fmt::Display`
    Classic,
    /// De Bruijn indices; used by `fmt::Debug`
    DeBruijn
}

/// A lambda term that is either a variable with a De Bruijn index, an abstraction over a term or
/// an applicaction of one term to another.
#[derive(PartialEq, Clone, Hash, Eq)]
pub enum Term {
    /// a variable
    Var(usize),
    /// an abstraction
    Abs(Box<Term>),
    /// an application
    App(Box<(Term, Term)>)
}

/// An error that can be returned when an inapplicable function is applied to a `Term`.
#[derive(Debug, PartialEq)]
pub enum TermError {
    /// the term is not a variable
    NotVar,
    /// the term is not an abstraction
    NotAbs,
    /// the term is not an application
    NotApp,
}

impl Term {
    /// Returns a variable's De Bruijn index, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar(), Ok(1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar(self) -> Result<usize, TermError> {
        if let Var(n) = self { Ok(n) } else { Err(NotVar) }
    }

    /// Returns a reference to a variable's De Bruijn index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar_ref(), Ok(&1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar_ref(&self) -> Result<&usize, TermError> {
        if let Var(ref n) = *self { Ok(n) } else { Err(NotVar) }
    }

    /// Returns a mutable reference to a variable's De Bruijn index.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Var(1).unvar_mut(), Ok(&mut 1));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not a `Var`iable.
    pub fn unvar_mut(&mut self) -> Result<&mut usize, TermError> {
        if let Var(ref mut n) = *self { Ok(n) } else { Err(NotVar) }
    }

    /// Returns an abstraction's underlying term, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs(self) -> Result<Term, TermError> {
        if let Abs(x) = self { Ok(*x) } else { Err(NotAbs) }
    }

    /// Returns a reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs_ref(), Ok(&Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs_ref(&self) -> Result<&Term, TermError> {
        if let Abs(ref x) = *self { Ok(x) } else { Err(NotAbs) }
    }

    /// Returns a mutable reference to an abstraction's underlying term.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(abs(Var(1)).unabs_mut(), Ok(&mut Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn unabs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Abs(ref mut x) = *self { Ok(x) } else { Err(NotAbs) }
    }

    /// Returns a pair containing an application's underlying terms, consuming it in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp(), Ok((Var(1), Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp(self) -> Result<(Term, Term), TermError> {
        if let App(boxed) = self {
            let (lhs, rhs) = *boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns a pair containing references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp_ref(), Ok((&Var(1), &Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp_ref(&self) -> Result<(&Term, &Term), TermError> {
        if let App(boxed) = self {
            let (ref lhs, ref rhs) = **boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns a pair containing mutable references to an application's underlying terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).unapp_mut(), Ok((&mut Var(1), &mut Var(2))));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn unapp_mut(&mut self) -> Result<(&mut Term, &mut Term), TermError> {
        if let App(boxed) = self {
            let (ref mut lhs, ref mut rhs) = **boxed;
            Ok((lhs, rhs))
        } else {
            Err(NotApp)
        }
    }

    /// Returns the left-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn lhs(self) -> Result<Term, TermError> {
        if let Ok((lhs, _)) = self.unapp() { Ok(lhs) } else { Err(NotApp) }
    }

    /// Returns a reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs_ref(), Ok(&Var(1)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn lhs_ref(&self) -> Result<&Term, TermError> {
        if let Ok((lhs, _)) = self.unapp_ref() { Ok(lhs) } else { Err(NotApp) }
    }

    /// Returns a mutable reference to the left-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).lhs_mut(), Ok(&mut Var(1)));
    /// ```
    pub fn lhs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Ok((lhs, _)) = self.unapp_mut() { Ok(lhs) } else { Err(NotApp) }
    }

    /// Returns the right-hand side term of an application. Consumes `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs(), Ok(Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs(self) -> Result<Term, TermError> {
        if let Ok((_, rhs)) = self.unapp() { Ok(rhs) } else { Err(NotApp) }
    }

    /// Returns a reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs_ref(), Ok(&Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs_ref(&self) -> Result<&Term, TermError> {
        if let Ok((_, rhs)) = self.unapp_ref() { Ok(rhs) } else { Err(NotApp) }
    }

    /// Returns a mutable reference to the right-hand side term of an application.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(app(Var(1), Var(2)).rhs_mut(), Ok(&mut Var(2)));
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `App`lication.
    pub fn rhs_mut(&mut self) -> Result<&mut Term, TermError> {
        if let Ok((_, rhs)) = self.unapp_mut() { Ok(rhs) } else { Err(NotApp) }
    }

    /// Returns `true` if `self` is a
    /// [supercombinator](https://en.wikipedia.org/wiki/Supercombinator).
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let term1 = abs(app(Var(1), abs(Var(1)))); // λ 1 (λ 1)
    /// let term2 = app(abs(Var(2)), abs(Var(1))); // (λ 2) (λ 1)
    ///
    /// assert_eq!(term1.is_supercombinator(), true);
    /// assert_eq!(term2.is_supercombinator(), false);
    /// ```
    pub fn is_supercombinator(&self) -> bool {
        let mut stack = vec![(0usize, self)];

        while let Some((depth, term)) = stack.pop() {
            match term {
                Var(i) => if *i > depth { return false },
                Abs(ref t) => stack.push((depth + 1, t)),
                App(boxed) => {
                    let (ref f, ref a) = **boxed;
                    stack.push((depth, f));
                    stack.push((depth, a))
                }
            }
        }
        true
    }

}

/// Wraps a `Term` in an `Abs`traction. Consumes its argument.
///
/// # Example
/// ```
/// use lambda_calculus::*;
///
/// assert_eq!(abs(Var(1)), Abs(Box::new(Var(1))));
/// ```
pub fn abs(term: Term) -> Term { Abs(Box::new(term)) }

/// Produces an `App`lication of two given `Term`s without any reduction, consuming them in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::*;
///
/// assert_eq!(app(Var(1), Var(2)), App(Box::new((Var(1), Var(2)))));
/// ```
pub fn app(lhs: Term, rhs: Term) -> Term { App(Box::new((lhs, rhs))) }

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence_cla(self, 0, 0))
    }
}

fn show_precedence_cla(term: &Term, context_precedence: usize, depth: u32) -> String {
    match term {
        Var(0) => {
            "undefined".to_owned()
        },
        Var(i) => {
            if depth >= *i as u32 {
                from_u32(depth + 97 - *i as u32).expect("error while printing term").to_string()
            } else {
                from_u32(96 + *i as u32).expect("error while printing term").to_string()
            }
        },
        Abs(ref t) => {
            let ret = {
                format!("{}{}.{}",
                    LAMBDA,
                    from_u32(depth + 97).expect("error while printing term"),
                    show_precedence_cla(t, 0, depth + 1)
                )
            };
            parenthesize_if(&ret, context_precedence > 1).into()
        },
        App(boxed) => {
            let (ref t1, ref t2) = **boxed;
            let ret = format!("{} {}",
                show_precedence_cla(t1, 2, depth),
                show_precedence_cla(t2, 3, depth)
            );
            parenthesize_if(&ret, context_precedence == 3).into()
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", show_precedence_dbr(self, 0, 0))
    }
}

fn show_precedence_dbr(term: &Term, context_precedence: usize, depth: u32) -> String {
    match term {
        Var(0) => {
            "undefined".to_owned()
        },
        Var(i) => {
            format!("{:X}", i)
        },
        Abs(ref t) => {
            let ret = format!("{}{:?}", LAMBDA, t);
            parenthesize_if(&ret, context_precedence > 1).into()
        },
        App(boxed) => {
            let (ref t1, ref t2) = **boxed;
            let ret = format!("{}{}",
                show_precedence_dbr(t1, 2, depth),
                show_precedence_dbr(t2, 3, depth)
            );
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
/// use lambda_calculus::term::*;
///
/// assert_eq!(app!(Var(1), Var(2), Var(3)), app(app(Var(1), Var(2)), Var(3)));
/// # }
/// ```
#[macro_export]
macro_rules! app {
    ($term1:expr, $($term2:expr),+) => {
        {
            let mut term = $term1;
            $(term = app(term, $term2);)*
            term
        }
    };
}

/// A macro for multiple abstraction of `Term`s.
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::*;
///
/// assert_eq!(abs!(3, Var(1)), abs(abs(abs(Var(1)))));
/// # }
/// ```
#[macro_export]
macro_rules! abs {
    ($n:expr, $term:expr) => {
        {
            let mut term = $term;

            for _ in 0..$n {
                term = abs(term);
            }

            term
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn app_macro() {
        assert_eq!(app!(Var(4), app!(Var(1), Var(2), Var(3))),
                   app(Var(4), app(app(Var(1), Var(2)), Var(3)))
        );
    }

    #[test]
    fn abs_macro() {
        assert_eq!(abs!(4, Var(1)),
                   abs(abs(abs(abs(Var(1)))))
        );

        assert_eq!(abs!(2, app(Var(1), Var(2))),
                   abs(abs(app(Var(1), Var(2))))
        );
    }

    #[test]
    fn open_term_display() {
        assert_eq!(&abs(Var(2)).to_string(),     "λa.b");
        assert_eq!(&abs(Var(3)).to_string(),     "λa.c");
        assert_eq!(&abs!(2, Var(3)).to_string(), "λa.λb.c");
        assert_eq!(&abs!(2, Var(4)).to_string(), "λa.λb.d");
    }

    #[test]
    fn display_modes() {
        let zero = abs!(2, Var(1));
        let succ = abs!(3, app(Var(2), app!(Var(3), Var(2), Var(1))));
        let pred = abs!(3, app!(
            Var(3),
            abs!(2, app(Var(1), app(Var(2), Var(4)))),
            abs(Var(2)),
            abs(Var(1))
        ));

        assert_eq!(&zero.to_string(), "λa.λb.b");
        assert_eq!(&succ.to_string(), "λa.λb.λc.b (a b c)");
        assert_eq!(&pred.to_string(), "λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)");

        assert_eq!(&format!("{:?}", zero), "λλ1");
        assert_eq!(&format!("{:?}", succ), "λλλ2(321)");
        assert_eq!(&format!("{:?}", pred), "λλλ3(λλ1(24))(λ2)(λ1)");
    }

    #[test]
    fn is_supercombinator() {
        assert_eq!(abs(Var(1)).is_supercombinator(), true);
        assert_eq!(app(abs(Var(1)), abs(Var(1))).is_supercombinator(), true);
        assert_eq!(abs!(10, Var(10)).is_supercombinator(), true);
        assert_eq!(abs!(10, app(Var(10), Var(10))).is_supercombinator(), true);

        assert_eq!(Var(1).is_supercombinator(), false);
        assert_eq!(abs(Var(2)).is_supercombinator(), false);
        assert_eq!(app(abs(Var(1)), Var(1)).is_supercombinator(), false);
        assert_eq!(abs!(10, Var(11)).is_supercombinator(), false);
        assert_eq!(abs!(10, app(Var(10), Var(11))).is_supercombinator(), false);
    }
}
