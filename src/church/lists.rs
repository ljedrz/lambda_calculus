//! [Church single-pair lists](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use term::{Term, Error, abs, app};
use term::Term::*;
use term::Error::*;
use church::booleans::{tru, fls};
use church::pairs::{pair, fst, snd};
use church::numerals::zero;
use combinators::z;
use std::ops::Index;
use std::mem;

/// Equivalent to `booleans::fls()`; produces a Church-encoded `nil`, the last
/// link of a Church list.
///
/// NIL := FALSE
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::nil;
///
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
/// use lambda_calculus::church::lists::{nil, null};
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(null(), nil()), NOR, 0, false), true.into());
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
/// use lambda_calculus::church::lists::{nil, cons};
/// use lambda_calculus::*;
///
/// let list_consed = beta(
///     app!(
///         cons(),
///         1.into(),
///         app!(
///             cons(),
///             2.into(),
///             app!(
///                 cons(),
///                 3.into(),
///                 nil()
///             )
///         )
///     ), NOR, 0, false
/// );
///
/// let list_from_vec = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(list_consed, list_from_vec);
/// ```
pub fn cons() -> Term { pair() }

/// Equivalent to `pairs::fst()`; applied to a Church list it returns its first element.
///
/// HEAD := FST
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::head;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app(head(), list), NOR, 0, false), 1.into());
/// ```
pub fn head() -> Term { fst() }

/// Equivalent to `pairs::snd()`; applied to a Church list it returns a new list with all its
/// elements but the first one.
///
/// TAIL := SND
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::tail;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(
///     beta(app(tail(), list), NOR, 0, false),
///     vec![2.into(), 3.into()].into()
/// );
/// ```
pub fn tail() -> Term { snd() }

/// Applied to a Church list it returns its Church-encoded length.
///
/// LENGTH := Z (λzal.NULL l (λx.a) (λx.z (SUCC a) (SND l)) I) ZERO
/// = Z (λλλ NULL 1 (λ 3) (λ 4 (SUCC 3) (SND 2)) I) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::{length, nil};
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);
///
/// assert_eq!(beta(app(length(), nil()), NOR, 0, false), 0.into());
/// assert_eq!(beta(app(length(), list ), NOR, 0, false), 4.into());
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
/// use lambda_calculus::church::lists::reverse;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(
///     beta(app(reverse(), list), NOR, 0, false),
///     vec![3.into(), 2.into(), 1.into()].into()
/// );
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
/// use lambda_calculus::church::lists::list;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(list(), 3.into(), 1.into(), 2.into(), 3.into()), NOR, 0, false),
///     vec![1.into(), 2.into(), 3.into()].into()
/// );
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
/// use lambda_calculus::church::lists::append;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![1.into(), 2.into()]);
/// let list2 = Term::from(vec![3.into(), 4.into()]);
///
/// assert_eq!(
///     beta(app!(append(), list1, list2), NOR, 0, false),
///     vec![1.into(), 2.into(), 3.into(), 4.into()].into()
/// );
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
/// use lambda_calculus::church::lists::index;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(index(), 0.into(), list.clone()), NOR, 0, false), 1.into());
/// assert_eq!(beta(app!(index(), 2.into(), list        ), NOR, 0, false), 3.into());
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
/// use lambda_calculus::church::lists::map;
/// use lambda_calculus::church::numerals::succ;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(
///     beta(app!(map(), succ(), list), NOR, 0, false),
///     vec![2.into(), 3.into(), 4.into()].into()
/// );
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
/// [left fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDL := Z (λzfsl. NULL l (λx.s) (λx.z f (f s (FST l)) (SND l)) I) =
/// Z (λ λ λ λ NULL 1 (λ 3) (λ 5 4 (4 3 (FST 2)) (SND 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::{foldl, nil};
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), list ), NOR, 0, false), 6.into());
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), nil()), NOR, 0, false), 0.into());
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
/// [right fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDR := λfsl. Z (λzt. NULL t (λx.s) (λx.f (FST t) (z (SND t))) I) l =
/// λ λ λ Z (λ λ NULL 1 (λ 5) (λ 6 (FST 2) (3 (SND 2))) I) 1
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::{foldr, nil};
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(foldr(), plus(), 0.into(), list ), NOR, 0, false), 6.into());
/// assert_eq!(beta(app!(foldr(), plus(), 0.into(), nil()), NOR, 0, false), 0.into());
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
/// use lambda_calculus::church::lists::{filter, nil};
/// use lambda_calculus::church::numerals::{is_zero, gt};
/// use lambda_calculus::combinators::c;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let gt_1 = app!(c(), gt(), 1.into()); // greater than 1
///
/// assert_eq!(
///     beta(app!(filter(), is_zero(), list.clone()), NOR, 0, false),
///     vec![0.into()].into()
/// );
/// assert_eq!(
///     beta(app!(filter(), gt_1, list), NOR, 0, false),
///     vec![2.into(), 3.into()].into()
/// );
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

/// Applied to a Church-encoded list it returns the last element.
///
/// LAST := Z (λzl.NULL l (λx.NIL) (λx.NULL (TAIL l) (HEAD l) (z (TAIL l))) I) =
/// Z (λ 2 1. NULL 1 (λ NIL) (λ NULL (TAIL 2) (HEAD 2) (3 (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::{last};
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app(last(), list), NOR, 0, false), 3.into());
/// ```
pub fn last() -> Term {
    app(
        z(),
        abs!(2, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(2),
                abs!(2, Var(1)),
                abs!(5, Var(1)),
                abs!(2, Var(2)),
                app(Var(2), abs!(2, Var(2))),
                app(Var(3), app(Var(2), abs!(2, Var(1))))
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a Church-encoded list it returns the list without the last element.
///
/// INIT := Z (λzl.NULL l (λx.NIL) (λx.(NULL (FST l) NIL (PAIR (FST l) (z (SND l))))) I) =
/// Z (λ λ NULL 1 (λ NIL) (λ (NULL (FST 2) NIL (PAIR (FST 2) (3 (SND 2))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::lists::init;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let list2 = Term::from(vec![0.into(), 1.into(), 2.into()]);
///
/// assert_eq!(beta(app(init(), list1), NOR, 0, false), list2);
/// ```
pub fn init() -> Term {
    app(
        z(),
        abs!(2, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(2),
                abs!(2, Var(1)),
                abs!(5, Var(1)),
                abs!(2, Var(2)),
                abs!(2, Var(1)),
                abs(app!(
                    Var(1),
                    app(Var(3), abs!(2, Var(2))),
                    app(Var(4), app(Var(3), abs!(2, Var(1))))
                ))
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

        let mut last_candidate = self.snd_ref()?;

        while let Ok(second) = last_candidate.snd_ref() {
            last_candidate = second;
        }

        Ok(last_candidate)
    }

    /// Checks whether `self` is a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert!(Term::from(vec![1.into(), 2.into(), 3.into()]).is_list());
    /// ```
    pub fn is_list(&self) -> bool {
        self.last_ref() == Ok(&nil())
    }

    /// Splits a Church list into a pair containing its first term and a list of all the
    /// other terms, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).uncons(),
    ///     Ok((1.into(), vec![2.into(), 3.into()].into()))
    /// );
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
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).uncons_ref(),
    ///     Ok((&1.into(), &vec![2.into(), 3.into()].into()))
    /// );
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
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).uncons_mut(),
    ///     Ok((&mut 1.into(), &mut vec![2.into(), 3.into()].into()))
    /// );
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
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).head(),
    ///     Ok(1.into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head(self) -> Result<Term, Error> {
        Ok(self.uncons()?.0)
    }

    /// Returns a reference to the first term of a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).head_ref(),
    ///     Ok(&1.into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head_ref(&self) -> Result<&Term, Error> {
        Ok(self.uncons_ref()?.0)
    }

    /// Returns a mutable reference to the first term of a Church list.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).head_mut(),
    ///     Ok(&mut 1.into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn head_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(self.uncons_mut()?.0)
    }

    /// Returns a list of all the terms of a Church list but the first one, consuming `self`.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).tail(),
    ///     Ok(vec![2.into(), 3.into()].into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail(self) -> Result<Term, Error> {
        Ok(self.uncons()?.1)
    }

    /// Returns a reference to a list of all the terms of a Church list but the first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).tail_ref(),
    ///     Ok(&vec![2.into(), 3.into()].into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail_ref(&self) -> Result<&Term, Error> {
        Ok(self.uncons_ref()?.1)
    }

    /// Returns a mutable reference to a list of all the terms of a Church list but the
    /// first one.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(
    ///     Term::from(vec![1.into(), 2.into(), 3.into()]).tail_mut(),
    ///     Ok(&mut vec![2.into(), 3.into()].into())
    /// );
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn tail_mut(&mut self) -> Result<&mut Term, Error> {
        Ok(self.uncons_mut()?.1)
    }

    /// Returns the length of a Church list
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// assert_eq!(Term::from(vec![1.into(), 2.into(), 3.into()]).len(), Ok(3));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn len(&self) -> Result<usize, Error> {
        let mut inner = self;
        let mut n = 0;

        while *inner != nil() {
            n += 1;
            inner = inner.tail_ref()?;
        }

        Ok(n)
    }

    /// Adds a term to the beginning of a Church list and returns the new list. Consumes
    /// `self` and the argument.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let list_from_vec = Term::from(vec![1.into(), 2.into(), 3.into()]);
    /// let list_pushed = Term::from(vec![])
    ///                   .push(3.into())
    ///                   .and_then(|t| t.push(2.into()))
    ///                   .and_then(|t| t.push(1.into()))
    ///                   .unwrap();
    ///
    /// assert_eq!(list_from_vec, list_pushed);
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
    /// use lambda_calculus::*;
    ///
    /// let mut list = Term::from(vec![1.into(), 2.into(), 3.into()]);
    ///
    /// assert_eq!(list.pop(), Ok(1.into()));
    /// assert_eq!(list, vec![2.into(), 3.into()].into());
    /// assert_eq!(list.pop(), Ok(2.into()));
    /// assert_eq!(list, vec![3.into()].into());
    /// assert_eq!(list.pop(), Ok(3.into()));
    /// assert_eq!(list, vec![].into());
    ///
    /// assert!(list.is_empty())
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not a Church list.
    pub fn pop(&mut self) -> Result<Term, Error> {
        let to_uncons = mem::replace(self, Var(0)); // replace self with a dummy
        let (head, tail) = to_uncons.uncons()?;
        mem::replace(self, tail); // replace self with tail

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

    #[test]
    fn list_length() {
        assert_eq!(nil().len(), Ok(0));
        assert_eq!(Term::from(vec![]).len(), Ok(0));
        assert_eq!(Term::from(vec![1.into()]).len(), Ok(1));
        assert_eq!(Term::from(vec![1.into(), 2.into()]).len(), Ok(2));
        assert_eq!(Term::from(vec![1.into(), 2.into(), 3.into()]).len(), Ok(3));
    }

    #[test]
    fn list_head_tail() {
        let list = Term::from(vec![1.into(), 2.into(), 3.into()]);

        assert_eq!(list.head_ref(), Ok(&1.into()));
        assert_eq!(list.tail_ref(), Ok(&vec![2.into(), 3.into()].into()));
        assert_eq!(
            list.tail_ref().and_then(|t| t.head_ref()),
            Ok(&2.into())
        );
        assert_eq!(
            list.tail_ref().and_then(|t| t.tail_ref()).and_then(|t| t.head_ref()),
            Ok(&3.into())
        );

        assert_eq!(list.uncons(), Ok((1.into(), vec![2.into(), 3.into()].into())));
    }

    #[test]
    fn iterating_list() {
        let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
        let mut iter = list.into_iter();

        assert_eq!(iter.next(), Some(1.into()));
        assert_eq!(iter.next(), Some(2.into()));
        assert_eq!(iter.next(), Some(3.into()));
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
