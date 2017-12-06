//! [Church pairs](https://en.wikipedia.org/wiki/Church_encoding#Church_pairs)

use term::{Term, Error, abs, app};
use term::Term::*;
use term::Error::*;
use church::booleans::{tru, fls};

/// Produces a Church-encoded pair; applying it to two other terms puts them inside it.
///
/// PAIR := λxyz.z x y = λ λ λ 1 3 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::pairs::pair;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(pair(), 1.into(), 2.into()), NOR, 0, false),
///     (1.into(), 2.into()).into()
/// );
/// # }
/// ```
pub fn pair() -> Term {
    abs!(3, app!(Var(1), Var(3), Var(2)))
}

/// Applied to a Church-encoded pair `(a, b)` it yields `a`.
///
/// FST := λp.p TRUE = λ 1 TRUE
///
/// # Example
/// ```
/// # extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::pairs::fst;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(fst(), (1.into(), 2.into()).into()), NOR, 0, false),
///     1.into()
/// );
/// # }
/// ```
pub fn fst() -> Term { abs(app(Var(1), tru())) }

/// Applied to a Church-encoded pair `(a, b)` it yields `b`.
///
/// SND := λp.p FALSE = λ 1 FALSE
///
/// # Example
/// ```
/// # extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::pairs::snd;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(snd(), (1.into(), 2.into()).into()), NOR, 0, false),
///     2.into()
/// );
/// # }
/// ```
pub fn snd() -> Term { abs(app(Var(1), fls())) }

/// Applied to a function and a Church-encoded pair `(a, b)` it uncurries it
/// and applies the function to `a` and then `b`.
///
/// UNCURRY := λf.λp.f (FST p) (SND p) = λ λ 2 (FST 1) (SND 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::pairs::uncurry;
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(uncurry(), plus(), (1.into(), 2.into()).into()), NOR, 0, false),
///     3.into()
/// );
/// # }
/// ```
pub fn uncurry() -> Term {
    abs!(2, app!(
        Var(2), 
        app(Var(1), tru()), 
        app(Var(1), fls())
    ))
}

impl Term {
    /// Checks whether `self` is a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert!(Term::from((1.into(), 2.into())).is_pair());
    /// # }
    /// ```
    pub fn is_pair(&self) -> bool {
        self.unpair_ref().is_ok()
    }

    /// Splits a Church-encoded pair into a pair of terms, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from((1.into(), 2.into())).unpair(),
    ///     Ok((1.into(), 2.into()))
    /// );
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn unpair(self) -> Result<(Term, Term), Error> {
        let candidate = if let Abs(abstracted) = self { *abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp() {
            Ok((wrapped_a.rhs()?, b))
        } else {
            Err(NotAPair)
        }
    }

    /// Splits a Church-encoded pair into a pair of references to its underlying terms.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from((1.into(), 2.into())).unpair_ref(),
    ///     Ok((&1.into(), &2.into()))
    /// );
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn unpair_ref(&self) -> Result<(&Term, &Term), Error> {
        let candidate = if let Abs(ref abstracted) = *self { abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp_ref() {
            Ok((wrapped_a.rhs_ref()?, b))
        } else {
            Err(NotAPair)
        }
    }

    /// Splits a Church-encoded pair into a pair of mutable references to its underlying terms.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from((1.into(), 2.into())).unpair_mut(),
    ///     Ok((&mut 1.into(), &mut 2.into()))
    /// );
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn unpair_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        let candidate = if let Abs(ref mut abstracted) = *self { abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp_mut() {
            Ok((wrapped_a.rhs_mut()?, b))
        } else {
            Err(NotAPair)
        }
    }

    /// Returns the first term from a Church-encoded pair, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).fst(), Ok(1.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn fst(self) -> Result<Term, Error> {
        Ok(self.unpair()?.0)
    }

    /// Returns a reference to the first term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).fst_ref(), Ok(&1.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn fst_ref(&self) -> Result<&Term, Error> {
        Ok(self.unpair_ref()?.0)
    }

    /// Returns a mutable reference to the first term of a Church-encoded pair.
    /// Returns a reference to the first term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).fst_mut(), Ok(&mut 1.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn fst_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(self.unpair_mut()?.0)
    }

    /// Returns the second term from a Church-encoded pair, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).snd(), Ok(2.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn snd(self) -> Result<Term, Error> {
        Ok(self.unpair()?.1)
    }

    /// Returns a reference to the second term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).snd_ref(), Ok(&2.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn snd_ref(&self) -> Result<&Term, Error> {
        Ok(self.unpair_ref()?.1)
    }

    /// Returns a mutable reference to the second term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from((1.into(), 2.into())).snd_mut(), Ok(&mut 2.into()));
    /// # }
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church pair.
    pub fn snd_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(self.unpair_mut()?.1)
    }
}

impl From<(Term, Term)> for Term {
    fn from((t1, t2): (Term, Term)) -> Self {
        abs(app!(Var(1), t1, t2))
    }
}
