//! [Church single-pair list](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use term::*;
use term::Term::*;
use term::Error::*;
use booleans::*;
use pair::*;
use arithmetic::{zero, succ};
use combinators::y;
use std::ops::Index;
use reduction::normalize;

/// Equivalent to `fls()`; produces a Church-encoded `nil`, the last link of a Church-encoded list.
///
/// NIL := FALSE
///
/// # Example
/// ```
/// use lambda_calculus::list::nil;
/// use lambda_calculus::booleans::fls;
///
/// assert_eq!(nil(), fls());
/// ```
pub fn nil() -> Term { fls() }

/// Applied to a Church-encoded list it determines if it is empty.
///
/// NULL := λl.l (λhtd.FALSE) TRUE = λ 1 (λ λ λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::list::{nil, null};
/// use lambda_calculus::booleans::tru;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(null().app(nil())), tru());
/// ```
pub fn null() -> Term {
    abs(
        Var(1)
        .app(abs(abs(abs(fls()))))
        .app(tru())
    )
}

/// Equivalent to `pair()`; applied to two terms it returns them contained in a Church-encoded list.
///
/// CONS := PAIR
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::list::{nil, cons};
/// use lambda_calculus::reduction::normalize;
///
/// let list_110_consed = normalize(
///    cons()
///    .app(one())
///    .app(
///        cons()
///        .app(one())
///        .app(
///            cons()
///            .app(zero())
///            .app(nil())
///           )
///      )
/// );
/// let list_110_from_vec = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(list_110_consed, list_110_from_vec);
/// ```
pub fn cons() -> Term { pair() }

/// Equivalent to `first()`; applied to a Church-encoded list it returns its first element.
///
/// HEAD := FIRST
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::list::head;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// let list_110 = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(normalize(head().app(list_110)), one());
/// ```
pub fn head() -> Term { first() }

/// Equivalent to `second()`; applied to a Church-encoded list it returns a new list with all its
/// elements but the first one.
///
/// TAIL := SECOND
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::list::tail;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// let list_110 = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(normalize(tail().app(list_110)), Term::from(vec![one(), zero()]));
/// ```
pub fn tail() -> Term { second() }

/// Applied to a Church-encoded list it returns its Church-encoded length.
///
/// LENGTH := Y (λgcx.NULL x c (g (SUCC c) (SECOND x))) ZERO
/// = Y (λλλ NULL 1 2 (3 (SUCC 2) (SECOND 1))) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::list::{length, nil};
/// use lambda_calculus::reduction::normalize;
///
/// let list_4 = Term::from(vec![1.into(), 1.into(), 0.into(), 1.into()]);
///
/// assert_eq!(normalize(length().app(nil())),  0.into());
/// assert_eq!(normalize(length().app(list_4)), 4.into());
/// ```
pub fn length() -> Term {
    y()
    .app(
        abs(abs(abs(
            null()
            .app(Var(1))
            .app(Var(2))
            .app(
                Var(3)
                .app(succ().app(Var(2)))
                .app(second().app(Var(1)))
            )
        )))
    )
    .app(zero())
}

/// Reverses a Church-encoded list.
///
/// REVERSE := Y (λgal.NULL l a (g (PAIR (FIRST l) a) (SECOND l))) NIL =
/// Y (λ λ λ NULL 1 2 (3 (PAIR (FIRST 1) 2) (SECOND 1))) NIL
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::list::reverse;
/// use lambda_calculus::arithmetic::{zero, one};
/// use lambda_calculus::reduction::normalize;
///
/// let list = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(normalize(reverse().app(list)), Term::from(vec![zero(), one(), one()]));
/// ```
pub fn reverse() -> Term {
    y()
    .app(
        abs(abs(abs(
            null()
            .app(Var(1))
            .app(Var(2))
            .app(
                Var(3)
                .app(
                    pair()
                    .app(first().app(Var(1)))
                    .app(Var(2))
                )
                .app(second().app(Var(1)))
            )
        )))
    )
    .app(nil())
}

/// Applied to a Church-encoded number `n` and `n` `Term`s it creates a Church-encoded list of
/// those terms.
///
/// LIST := λn.n (λfax.f (PAIR x a)) REVERSE NIL = λ 1 (λ λ λ 3 (PAIR 1 2)) REVERSE NIL
///
/// # Example
/// ```
/// use lambda_calculus::term::Term;
/// use lambda_calculus::list::list;
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(list().app(3.into()).app(0.into()).app(1.into()).app(1.into())),
///            Term::from(vec![0.into(), 1.into(), 1.into()]));
/// ```
pub fn list() -> Term {
    abs(
        Var(1)
        .app(
            abs(abs(abs(
                Var(3).app(
                    pair()
                    .app(Var(1))
                    .app(Var(2))
                )
            )))
        )
        .app(reverse())
        .app(nil())
    )
}

impl Term {
    /// Checks whether self is a Church-encoded empty list, i.e. `nil()`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::list::nil;
    ///
    /// assert!(nil().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        *self == nil()
    }

    // Returns a reference to the last term of a Church-encoded list.
    fn last_ref(&self) -> Result<&Term, Error> {
        if !self.is_pair() { return Err(NotAList) }

        let mut last_candidate = try!(self.snd_ref());

        while let Ok(ref second) = last_candidate.snd_ref() {
            last_candidate = *second;
        }

        Ok(last_candidate)
    }

    /// Checks whether `self` is a Church-encoded list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert!(list_110.is_list());
    /// ```
    pub fn is_list(&self) -> bool {
        self.last_ref() == Ok(&nil())
    }

    /// Splits a Church-encoded list into a pair containing its first term and a list of all the
    /// other terms, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons(), Ok((one(), Term::from(vec![one(), zero()]))));
    /// ```
    pub fn uncons(self) -> Result<(Term, Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair()
        }
    }

    /// Splits a Church-encoded list into a pair containing references to its first term and a to
    /// list of all the other terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons_ref(), Ok((&one(), &Term::from(vec![one(), zero()]))));
    /// ```
    pub fn uncons_ref(&self) -> Result<(&Term, &Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair_ref()
        }
    }

    /// Splits a Church-encoded list into a pair containing mutable references to its first term
    /// and a to list of all the other terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons_ref_mut(),
    ///            Ok((&mut one(), &mut Term::from(vec![one(), zero()]))));
    /// ```
    pub fn uncons_ref_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair_ref_mut()
        }
    }

    /// Returns the first term from a Church-encoded list, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head(), Ok(one()));
    /// ```
    pub fn head(self) -> Result<Term, Error> {
        Ok(try!(self.uncons()).0)
    }

    /// Returns a reference to the first term of a Church-encoded list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head_ref(), Ok(&one()));
    /// ```
    pub fn head_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.uncons_ref()).0)
    }

    /// Returns a mutable reference to the first term of a Church-encoded list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head_ref_mut(), Ok(&mut one()));
    /// ```
    pub fn head_ref_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.uncons_ref_mut()).0)
    }

    /// Returns a list of all the terms of a Church-encoded list but the first one, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail(), Ok(Term::from(vec![one(), zero()])));
    /// ```
    pub fn tail(self) -> Result<Term, Error> {
        Ok(try!(self.uncons()).1)
    }

    /// Returns a reference to a list of all the terms of a Church-encoded list but the first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail_ref(), Ok(&Term::from(vec![one(), zero()])));
    /// ```
    pub fn tail_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.uncons_ref()).1)
    }

    /// Returns a mutable reference to a list of all the terms of a Church-encoded list but the
    /// first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail_ref_mut(), Ok(&mut Term::from(vec![one(), zero()])));
    /// ```
    pub fn tail_ref_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.uncons_ref_mut()).1)
    }

    /// Returns the length of a Church-encoded list
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.len(), Ok(3));
    /// ```
    pub fn len(&self) -> Result<usize, Error> {
        let mut inner = self;
        let mut n = 0;

        while *inner != nil() {
            n += 1;
            inner = try!(inner.tail_ref());
        }

        Ok(n)
    }

    /// Adds a term to the beginning of a Church-encoded list and returns the new list. Consumes
    /// `self` and the argument.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.push(zero()), Term::from(vec![zero(), one(), one(), zero()]));
    /// ```
    pub fn push(self, term: Term) -> Term {
        abs(Var(1).app(term).app(self))
    }

    /// Removes the first element from a Church-encoded list and returns it.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::arithmetic::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.pop(), Ok(one()));
    /// assert_eq!(list_110, Term::from(vec![one(), zero()]));
    /// ```
    pub fn pop(&mut self) -> Result<Term, Error> {
        let (head, tail) = try!(self.clone().uncons()); // TODO: drop clone()
        *self = tail;

        Ok(head)
    }
}

impl From<Vec<Term>> for Term {
    fn from(terms: Vec<Term>) -> Self {
        let mut output = nil();

        for term in terms.into_iter().rev() {
            output = output.push(term);
        }

        normalize(output)
    }
}

impl Iterator for Term {
    type Item = Term;

    fn next(&mut self) -> Option<Term> {
        if self.is_empty() {
            None
        } else {
            Some(self.pop().unwrap())
        }
    }
}

impl Index<usize> for Term {
    type Output = Term;

    fn index(&self, i: usize) -> &Self::Output {
        if !self.is_list() { panic!("attempting to index something that is not a list!") }

        if i == 0 { return self.head_ref().unwrap() } // safe - checked above

        let mut candidate = self.snd_ref().expect("index out of bounds!");

        for _ in 1..i {
            candidate = candidate.snd_ref().expect("index out of bounds!")
        }

        candidate.head_ref().unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use reduction::normalize;

    #[test]
    fn empty_list() {
        let nil = nil();

        assert!(!nil.is_list());
        assert!(nil.is_empty());
    }

    #[test]
    fn list_push() {
        let list_pushed = nil().push(0.into()).push(1.into()).push(1.into());
        let list_consed = normalize(
            cons().app(1.into()).app(cons().app(1.into()).app(cons().app(0.into()).app(nil())))
        );

        assert_eq!(list_pushed, list_consed);
    }

    #[test]
    fn list_from_vector() {
        let list_from_vec = Term::from(vec![1.into(), 1.into(), 0.into()]);
        let list_pushed = nil().push(0.into()).push(1.into()).push(1.into());

        assert_eq!(list_from_vec, list_pushed);
    }

    #[test]
    fn list_length() {
        let list0 = nil();
        assert_eq!(list0.len(), Ok(0));
        let list1 = list0.push(1.into());
        assert_eq!(list1.len(), Ok(1));
        let list2 = list1.push(1.into());
        assert_eq!(list2.len(), Ok(2));
        let list3 = list2.push(1.into());
        assert_eq!(list3.len(), Ok(3));
    }

    #[test]
    fn list_operations() {
        let list_354 = Term::from(vec![3.into(), 5.into(), 4.into()]);

        assert!(list_354.is_list());

        assert_eq!(list_354.head_ref(), Ok(&3.into()));
        assert_eq!(list_354.tail_ref(), Ok(&Term::from(vec![5.into(), 4.into()])));

        assert_eq!(list_354.tail_ref().and_then(|t| t.head_ref()), Ok(&5.into()));
        assert_eq!(list_354.tail_ref()
                   .and_then(|t| t.tail_ref())
                   .and_then(|t| t.head_ref()), Ok(&4.into()));

        let unconsed = list_354.uncons();
        assert_eq!(unconsed, Ok((3.into(), Term::from(vec![5.into(), 4.into()]))));
    }


    #[test]
    fn list_pop() {
        let mut list_poppable = Term::from(vec![1.into(), 0.into(), 0.into()]);

        assert_eq!(list_poppable.pop(), Ok(1.into()));
        assert_eq!(list_poppable.pop(), Ok(0.into()));
        assert_eq!(list_poppable.pop(), Ok(0.into()));
        assert_eq!(list_poppable.pop(), Err(NotAList));
    }

    #[test]
    fn iterating_list() {
        let list010 = Term::from(vec![0.into(), 1.into(), 0.into()]);
        let mut iter = list010.into_iter();

        assert_eq!(iter.next(), Some(0.into()));
        assert_eq!(iter.next(), Some(1.into()));
        assert_eq!(iter.next(), Some(0.into()));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn indexing_list() {
        let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into(), 4.into()]);

        assert_eq!(list[0], 0.into());
        assert_eq!(list[1], 1.into());
        assert_eq!(list[2], 2.into());
        assert_eq!(list[3], 3.into());
        assert_eq!(list[4], 4.into());
    }
}
