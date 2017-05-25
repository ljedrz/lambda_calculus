//! [Church pair](https://en.wikipedia.org/wiki/Church_encoding#Church_pairs)

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;

/// Produces a Church-encoded pair; applying it to two other terms puts them inside it.
///
/// PAIR := λxyz.z x y = λ λ λ 1 3 2
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::pair::pair;
/// use lambda_calculus::arithmetic::{zero, one};
///
/// let pair01 = app!(pair(), zero(), one());
///
/// assert_eq!(pair01.fst_ref(), Ok(&zero()));
/// assert_eq!(pair01.snd_ref(), Ok(&one()));
/// # }
/// ```
pub fn pair() -> Term {
    abs(abs(abs(
        app!(Var(1), Var(3), Var(2))
    )))
}

/// Applied to a Church-encoded pair `(a, b)` it yields `a`.
///
/// FST := λp.p TRUE = λ 1 TRUE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::pair::{pair, fst};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let pair_0_1 = app!(pair(), zero(), one());
///
/// assert_eq!(beta(fst().app(pair_0_1), NOR, 0), zero());
/// # }
/// ```
pub fn fst() -> Term { abs(Var(1).app(tru())) }

/// Applied to a Church-encoded pair `(a, b)` it yields `b`.
///
/// SND := λp.p FALSE = λ 1 FALSE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::pair::{pair, snd};
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let pair_0_1 = app!(pair(), zero(), one());
///
/// assert_eq!(beta(snd().app(pair_0_1), NOR, 0), one());
/// # }
/// ```
pub fn snd() -> Term { abs(Var(1).app(fls())) }

impl Term {
    /// Checks whether `self` is a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert!(pair01.is_pair());
    /// # }
    /// ```
    pub fn is_pair(&self) -> bool {
        self.unpair_ref().is_ok()
    }

    /// Splits a Church-encoded pair into a pair of terms, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.unpair(), Ok((zero(), one())));
    /// # }
    /// ```
    pub fn unpair(self) -> Result<(Term, Term), Error> {
        let candidate = if let Abs(abstracted) = self { *abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp() {
            Ok((try!(wrapped_a.rhs()), b))
        } else {
            Err(NotAPair)
        }
    }

    /// Splits a Church-encoded pair into a pair of references to its underlying terms.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.unpair_ref(), Ok((&zero(), &one())));
    /// # }
    /// ```
    pub fn unpair_ref(&self) -> Result<(&Term, &Term), Error> {
        let candidate = if let Abs(ref abstracted) = *self { abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp_ref() {
            Ok((try!(wrapped_a.rhs_ref()), b))
        } else {
            Err(NotAPair)
        }
    }

    /// Splits a Church-encoded pair into a pair of mutable references to its underlying terms.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.unpair_ref_mut(), Ok((&mut zero(), &mut one())));
    /// # }
    /// ```
    pub fn unpair_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        let mut candidate = if let Abs(ref mut abstracted) = *self { abstracted } else { self };

        if let Ok((wrapped_a, b)) = candidate.unapp_ref_mut() {
            Ok((try!(wrapped_a.rhs_ref_mut()), b))
        } else {
            Err(NotAPair)
        }
    }

    /// Returns the first term from a Church-encoded pair, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.fst(), Ok(zero()));
    /// # }
    /// ```
    pub fn fst(self) -> Result<Term, Error> {
        Ok(try!(self.unpair()).0)
    }

    /// Returns a reference to the first term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.fst_ref(), Ok(&zero()));
    /// # }
    /// ```
    pub fn fst_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.unpair_ref()).0)
    }

    /// Returns a mutable reference to the first term of a Church-encoded pair.
    /// Returns a reference to the first term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.fst_ref_mut(), Ok(&mut zero()));
    /// # }
    /// ```
    pub fn fst_ref_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.unpair_ref_mut()).0)
    }

    /// Returns the second term from a Church-encoded pair, consuming `self`.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.snd(), Ok(one()));
    /// # }
    /// ```
    pub fn snd(self) -> Result<Term, Error> {
        Ok(try!(self.unpair()).1)
    }

    /// Returns a reference to the second term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.snd_ref(), Ok(&one()));
    /// # }
    /// ```
    pub fn snd_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.unpair_ref()).1)
    }

    /// Returns a mutable reference to the second term of a Church-encoded pair.
    ///
    /// # Example
    /// ```
    /// # #[macro_use] extern crate lambda_calculus;
    /// # fn main() {
    /// use lambda_calculus::pair::pair;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut pair01 = app!(pair(), zero(), one());
    ///
    /// assert_eq!(pair01.snd_ref_mut(), Ok(&mut one()));
    /// # }
    /// ```
    pub fn snd_ref_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.unpair_ref_mut()).1)
    }
}

impl From<(Term, Term)> for Term {
    fn from((t1, t2): (Term, Term)) -> Self {
        abs(app!(Var(1), t1, t2))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use reduction::beta;
    use reduction::Order::*;

    #[test]
    fn pair_from_pair() {
        assert_eq!(Term::from((0.into(), 1.into())),
                   beta(app!(pair(), 0.into(), 1.into()), NOR, 0));
    }

    #[test]
    fn pair_operations() {
        let pair_four_three = beta(app!(pair(), 4.into(), 3.into()), NOR, 0);

        assert!(pair_four_three.is_pair());

        assert_eq!(pair_four_three.fst_ref(), Ok(&4.into()));
        assert_eq!(pair_four_three.snd_ref(), Ok(&3.into()));

        let unpaired = pair_four_three.unpair();
        assert_eq!(unpaired, Ok((4.into(), 3.into())));
    }
}

