//! [Church single-pair lists](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use term::{Term, Error, abs, app};
use term::Term::*;
use term::Error::*;
use church::booleans::{tru, fls};
use church::pairs::{pair, fst, snd};
use church::numerals::zero;
use combinators::z;
use std::ops::Index;

/// Equivalent to `booleans::fls()`; produces a Church-encoded `nil`, the last link of a
/// Church list.
///
/// NIL := FALSE
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::nil;
/// use lambda_calculus::church::booleans::fls;
///
/// assert_eq!(nil(), fls());
/// assert!(!nil().is_list());
/// assert!(nil().is_empty());
/// ```
pub fn nil() -> Term { fls() }

/// Applied to a Church list it determines if it is empty.
///
/// NULL := λl.l (λhtd.FALSE) TRUE = λ 1 (λ λ λ FALSE) TRUE
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::church::lists::{nil, null};
/// use lambda_calculus::church::booleans::tru;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(null(), nil()), NOR, 0, false), tru());
/// # }
/// ```
pub fn null() -> Term {
    abs(app!(Var(1), abs!(3, fls()), tru()))
}

/// Equivalent to `pairs::pair()`; applied to two terms it returns them contained in a Church list.
///
/// CONS := PAIR
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::numerals::{zero, one};
/// use lambda_calculus::church::lists::{nil, cons};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list_110_consed = beta(
///     app!(
///         cons(),
///         one(),
///         app!(
///             cons(),
///             one(),
///             app!(
///                 cons(),
///                 zero(),
///                 nil()
///             )
///         )
///     ), NOR, 0, false
/// );
/// let list_110_from_vec = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(list_110_consed, list_110_from_vec);
/// # }
/// ```
pub fn cons() -> Term { pair() }

/// Equivalent to `pairs::fst()`; applied to a Church list it returns its first element.
///
/// HEAD := FST
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::head;
/// use lambda_calculus::church::numerals::{zero, one};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list_110 = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(beta(app!(head(), list_110), NOR, 0, false), one());
/// # }
/// ```
pub fn head() -> Term { fst() }

/// Equivalent to `pairs::snd()`; applied to a Church list it returns a new list with all its
/// elements but the first one.
///
/// TAIL := SND
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::tail;
/// use lambda_calculus::church::numerals::{zero, one};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list_110 = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(beta(app!(tail(), list_110), NOR, 0, false), Term::from(vec![one(), zero()]));
/// # }
/// ```
pub fn tail() -> Term { snd() }

/// Applied to a Church list it returns its Church-encoded length.
///
/// LENGTH := Z (λzal.NULL l (λx.a) (λx.z (SUCC a) (SND l)) I) ZERO
/// = Z (λλλ NULL 1 (λ 3) (λ 4 (SUCC 3) (SND 2)) I) ZERO
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::{length, nil};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list_4 = Term::from(vec![1.into(), 1.into(), 0.into(), 1.into()]);
///
/// assert_eq!(beta(app!(length(), nil() ), NOR, 0, false), 0.into());
/// assert_eq!(beta(app!(length(), list_4), NOR, 0, false), 4.into());
/// # }
/// ```
pub fn length() -> Term {
    app!(
        z(),
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs(Var(3)),
            abs(app!(
                Var(4),
                abs!(2, app(Var(2), app!(Var(5), Var(2), Var(1)))),
                app(Var(2), abs!(2, Var(1)))
            )),
            abs(Var(1))
        )),
        zero()
    )
}

/// Reverses a Church list.
///
/// REVERSE := Z (λzal.NULL l (λx.a) (λx.z (PAIR (FST l) a) (SND l) I)) NIL =
/// Z (λ λ λ NULL 1 (λ 3) (λ 4 (PAIR (FST 2) 3) (SND 2)) I) NIL
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::reverse;
/// use lambda_calculus::church::numerals::{zero, one};
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![one(), one(), zero()]);
///
/// assert_eq!(beta(app!(reverse(), list), NOR, 0, false),
///            Term::from(vec![zero(), one(), one()])
/// );
/// # }
/// ```
pub fn reverse() -> Term {
    app!(
        z(),
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs(Var(3)),
            abs(app!(
                Var(4),
                abs(app!(
                    Var(1),
                    app(Var(3), abs!(2, Var(2))),
                    Var(4)
                )),
                app(Var(2), abs!(2, Var(1)))
            )),
            abs(Var(1))
        )),
        nil()
    )
}

/// Applied to a Church number `n` and `n` `Term`s it creates a Church list of
/// those terms.
///
/// LIST := λn.n (λfax.f (PAIR x a)) REVERSE NIL = λ 1 (λ λ λ 3 (PAIR 1 2)) REVERSE NIL
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::list;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// assert_eq!(beta(app!(list(), 3.into(), 0.into(), 1.into(), 1.into()), NOR, 0, false),
///            Term::from(vec![0.into(), 1.into(), 1.into()]));
/// # }
/// ```
pub fn list() -> Term {
    abs(app!(
        Var(1),
        abs!(3, app(Var(3), app!(pair(), Var(1), Var(2)))),
        reverse(),
        nil()
    ))
}

/// Applied to 2 Church lists it concatenates them.
///
/// APPEND := Z (λzab. NULL a (λx.b) (λx.PAIR (FST a) (z (SND a) b)) I) =
/// Z (λ λ λ NULL 2 (λ 2) (λ PAIR (FST 3) (4 (SND 3) 2)) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::append;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list1 = Term::from(vec![0.into(), 1.into()]);
/// let list2 = Term::from(vec![2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(append(), list1, list2), NOR, 0, false),
///            Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]));
/// # }
/// ```
pub fn append() -> Term {
    z().app(
        abs!(3, app!(
            Var(2),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs(Var(2)),
            abs!(2, app!(
                Var(1),
                app(Var(4), abs!(2, Var(2))),
                app!(
                    Var(5),
                    app(Var(4), abs!(2, Var(1))),
                    Var(3)
                )
            )),
            Var(1)
        ))
    )
}

/// Applied to a Church number `i` and a Church list it returns the `i`-th
/// (zero-indexed) element of the list.
///
/// INDEX := λil. FST (l SND i) = λ λ FST (2 SND 1)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::index;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![3.into(), 4.into(), 5.into()]);
///
/// assert_eq!(beta(app!(index(), 0.into(), list.clone()), NOR, 0, false), 3.into());
/// assert_eq!(beta(app!(index(), 2.into(), list        ), NOR, 0, false), 5.into());
/// # }
/// ```
pub fn index() -> Term {
    abs!(2, app!(
        Var(2),
        abs(app(Var(1), abs!(2, Var(1)))),
        Var(1),
        abs!(2, Var(2))
    ))
}

/// Applied to a function and a Church list it maps the function over it.
///
/// MAP := Z (λzfl. NULL l (λx.NIL) (λx.PAIR (f (FST l)) (z f (SND l))) I) =
/// Z (λ λ λ NULL 1 (λ NIL) (λ PAIR (3 (FST 2)) (4 3 (SND 2))) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::map;
/// use lambda_calculus::church::numerals::succ;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(map(), succ(), list), NOR, 0, false),
///            Term::from(vec![2.into(), 3.into(), 4.into()]));
/// # }
/// ```
pub fn map() -> Term {
    z().app(
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs!(2, app!(
                Var(1),
                app(
                    Var(4),
                    app(Var(3), abs!(2, Var(2)))
                ),
                app!(
                    Var(5),
                    Var(4),
                    app(Var(3), abs!(2, Var(1)))
                )
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a function, a starting value and a Church list it performs a
/// [left fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists) on the
/// list.
///
/// FOLDL := Z (λzfsl. NULL l (λx.s) (λx.z f (f s (FST l)) (SND l)) I) =
/// Z (λ λ λ λ NULL 1 (λ 3) (λ 5 4 (4 3 (FST 2)) (SND 2)) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::{foldl, nil};
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), list ), NOR, 0, false), 6.into());
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), nil()), NOR, 0, false), 0.into());
/// # }
/// ```
pub fn foldl() -> Term {
    z().app(
        abs!(4, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs(Var(3)),
            abs(app!(
                Var(5),
                Var(4),
                app!(
                    Var(4),
                    Var(3),
                    app(Var(2), abs!(2, Var(2)))
                ),
                app(Var(2), abs!(2, Var(1)))
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a function, a starting value and a Church list it performs a
/// [right fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists) on the
/// list.
///
/// FOLDR := λfsl. Z (λzt. NULL t (λx.s) (λx.f (FST t) (z (SND t))) I) l =
/// λ λ λ Z (λ λ NULL 1 (λ 5) (λ 6 (FST 2) (3 (SND 2))) I) 1
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::{foldr, nil};
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(foldr(), plus(), 0.into(), list ), NOR, 0, false), 6.into());
/// assert_eq!(beta(app!(foldr(), plus(), 0.into(), nil()), NOR, 0, false), 0.into());
/// # }
/// ```
pub fn foldr() -> Term {
    abs!(3, app!(
        z(),
        abs!(2, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs(Var(5)),
            abs(app!(
                Var(6),
                app(Var(2), abs!(2, Var(2))),
                app(Var(3), app(Var(2), abs!(2, Var(1))))
            )),
            abs(Var(1))
        )),
        Var(1)
    ))
}

/// Applied to a predicate and a Church list it filters the list based on the predicate.
///
/// FILTER := Z (λzpl. NULL l (λx.NIL) (λx.p (FST l) (PAIR (FST l)) I (z p (SND l))) I) =
/// Z (λ λ λ NULL 1 (λ NIL) (λ 3 (FST 2) (PAIR (FST 2)) I (4 3 (SND 2))) I)
///
/// # Example
/// ```
/// # #[macro_use] extern crate lambda_calculus;
/// # fn main() {
/// use lambda_calculus::term::Term;
/// use lambda_calculus::church::lists::{filter, nil};
/// use lambda_calculus::church::numerals::{is_zero, gt};
/// use lambda_calculus::combinators::c;
/// use lambda_calculus::reduction::beta;
/// use lambda_calculus::reduction::Order::*;
///
/// let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let gt1  = app!(c(), gt(), 1.into());
///
/// assert_eq!(beta(app!(filter(), is_zero(), list.clone()), NOR, 0, false),
///            Term::from(vec![0.into()]));
/// assert_eq!(beta(app!(filter(), gt1, list), NOR, 0, false),
///            Term::from(vec![2.into(), 3.into()]));
/// # }
/// ```
pub fn filter() -> Term {
    z().app(
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(3),
                app(Var(2), abs!(2, Var(2))),
                abs!(2, app!(
                    Var(1),
                    app(Var(4), abs!(2, Var(2))),
                    Var(2)
                )),
                abs(Var(1)),
                app!(
                    Var(4),
                    Var(3),
                    app(Var(2), abs!(2, Var(1)))
                )
            )),
            abs(Var(1))
        ))
    )
}

impl Term {
    /// Checks whether self is a empty Church list, i.e. `nil()`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::church::lists::nil;
    ///
    /// assert!(nil().is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        *self == nil()
    }

    // Returns a reference to the last term of a Church list.
    fn last_ref(&self) -> Result<&Term, Error> {
        if !self.is_pair() { return Err(NotAList) }

        let mut last_candidate = try!(self.snd_ref());

        while let Ok(second) = last_candidate.snd_ref() {
            last_candidate = second;
        }

        Ok(last_candidate)
    }

    /// Checks whether `self` is a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert!(list_110.is_list());
    /// ```
    pub fn is_list(&self) -> bool {
        self.last_ref() == Ok(&nil())
    }

    /// Splits a Church list into a pair containing its first term and a list of all the
    /// other terms, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons(), Ok((one(), Term::from(vec![one(), zero()]))));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn uncons(self) -> Result<(Term, Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair()
        }
    }

    /// Splits a Church list into a pair containing references to its first term and a to
    /// list of all the other terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons_ref(), Ok((&one(), &Term::from(vec![one(), zero()]))));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn uncons_ref(&self) -> Result<(&Term, &Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair_ref()
        }
    }

    /// Splits a Church list into a pair containing mutable references to its first term
    /// and a to list of all the other terms.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.uncons_mut(),
    ///            Ok((&mut one(), &mut Term::from(vec![one(), zero()]))));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn uncons_mut(&mut self) -> Result<(&mut Term, &mut Term), Error> {
        if !self.is_list() {
            Err(NotAList)
        } else {
            self.unpair_mut()
        }
    }

    /// Returns the first term from a Church list, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head(), Ok(one()));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head(self) -> Result<Term, Error> {
        Ok(try!(self.uncons()).0)
    }

    /// Returns a reference to the first term of a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head_ref(), Ok(&one()));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.uncons_ref()).0)
    }

    /// Returns a mutable reference to the first term of a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.head_mut(), Ok(&mut one()));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.uncons_mut()).0)
    }

    /// Returns a list of all the terms of a Church list but the first one, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail(), Ok(Term::from(vec![one(), zero()])));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail(self) -> Result<Term, Error> {
        Ok(try!(self.uncons()).1)
    }

    /// Returns a reference to a list of all the terms of a Church list but the first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail_ref(), Ok(&Term::from(vec![one(), zero()])));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail_ref(&self) -> Result<&Term, Error> {
        Ok(try!(self.uncons_ref()).1)
    }

    /// Returns a mutable reference to a list of all the terms of a Church list but the
    /// first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.tail_mut(), Ok(&mut Term::from(vec![one(), zero()])));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(try!(self.uncons_mut()).1)
    }

    /// Returns the length of a Church list
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.len(), Ok(3));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn len(&self) -> Result<usize, Error> {
        let mut inner = self;
        let mut n = 0;

        while *inner != nil() {
            n += 1;
            inner = try!(inner.tail_ref());
        }

        Ok(n)
    }

    /// Adds a term to the beginning of a Church list and returns the new list. Consumes
    /// `self` and the argument.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.push(zero()), Ok(Term::from(vec![zero(), one(), one(), zero()])));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list or a `nil()`.
    pub fn push(self, term: Term) -> Result<Term, Error> {
        if !self.is_list() && self != nil() { return Err(NotAList) }

        Ok(abs(app!(Var(1), term, self)))
    }

    /// Removes the first element from a Church list and returns it.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::Term;
    /// use lambda_calculus::church::numerals::{zero, one};
    ///
    /// let mut list_110 = Term::from(vec![one(), one(), zero()]);
    ///
    /// assert_eq!(list_110.pop(), Ok(one()));
    /// assert_eq!(list_110, Term::from(vec![one(), zero()]));
    /// assert_eq!(list_110.pop(), Ok(one()));
    /// assert_eq!(list_110, Term::from(vec![zero()]));
    /// assert_eq!(list_110.pop(), Ok(zero()));
    /// assert_eq!(list_110, Term::from(vec![]));
    ///
    /// assert!(list_110.is_empty())
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn pop(&mut self) -> Result<Term, Error> {
        let (head, tail) = try!(self.clone().uncons()); // TODO: drop clone()?
        *self = tail;

        Ok(head)
    }
}

impl From<Vec<Term>> for Term {
    fn from(terms: Vec<Term>) -> Self {
        let mut output = nil();

        for term in terms.into_iter().rev() {
            output = output.push(term).unwrap(); // safe - built from nil()
        }

        output
    }
}

impl Iterator for Term {
    type Item = Term;

    fn next(&mut self) -> Option<Term> {
        if self.is_empty() {
            None
        } else {
            Some(self.pop().unwrap()) // safe; ensured above
        }
    }
}

impl Index<usize> for Term {
    type Output = Term;

    fn index(&self, i: usize) -> &Self::Output {
        if !self.is_list() { panic!("attempting to index something that is not a list!") }

        if i == 0 { return self.head_ref().unwrap() } // safe - guaranteed by is_list()

        let mut candidate = self.snd_ref().expect("index out of bounds!");

        for _ in 1..i {
            candidate = candidate.snd_ref().expect("index out of bounds!")
        }

        candidate.head_ref().unwrap() // safe - verified as valid by is_list()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use reduction::beta;
    use reduction::Order::*;
    use church::numerals::{is_zero, plus, succ};

    #[test]
    fn list_from_vector() {
        let list_from_vec = Term::from(vec![1.into(), 1.into(), 0.into()]);
        let list_pushed = nil()
            .push(0.into())
            .and_then(|t| t.push(1.into()))
            .and_then(|t| t.push(1.into()))
            .unwrap();

        assert_eq!(list_from_vec, list_pushed);
    }

    #[test]
    fn list_length() {
        let list0 = nil();
        assert_eq!(list0.len(), Ok(0));
        let list1 = list0.push(1.into()).unwrap();
        assert_eq!(list1.len(), Ok(1));
        let list2 = list1.push(1.into()).unwrap();
        assert_eq!(list2.len(), Ok(2));
        let list3 = list2.push(1.into()).unwrap();
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

    #[test]
    fn cbv_list_functions() {
        let l = Term::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);

        assert_eq!(beta(app!( length(), l.clone()), HAP, 0, false), 4.into());

        assert_eq!(beta(app!(reverse(), l.clone()), HAP, 0, false),
            Term::from(vec![4.into(), 3.into(), 2.into(), 1.into()]));

        assert_eq!(beta(app!(list(), 4.into(), 1.into(), 2.into(), 3.into(), 4.into()), HAP, 0, false), l);

        assert_eq!(beta(app!(append(), Term::from(vec![1.into(), 2.into()]),
            Term::from(vec![3.into(), 4.into()])), HAP, 0, false), l);

        assert_eq!(beta(app!(map(), succ(), l.clone()), HAP, 0, false),
            Term::from(vec![2.into(), 3.into(), 4.into(), 5.into()]));

        assert_eq!(beta(app!(foldl(), plus(), 0.into(), l.clone()), HAP, 0, false), 10.into());
        assert_eq!(beta(app!(foldr(), plus(), 0.into(), l.clone()), HAP, 0, false), 10.into());

        assert_eq!(beta(app!(filter(), is_zero(), l.clone()), HAP, 0, false), Term::from(vec![]));
    }
}
