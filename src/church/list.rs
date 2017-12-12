//! [Church single-pair lists](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use term::{Term, abs, app};
use term::Term::*;
use church::boolean::{tru, fls};
use church::pair::{pair, fst, snd};
use church::numerals::zero;
use combinators::Z;

/// Equivalent to `booleans::fls()`; produces a Church-encoded `nil`, the last
/// link of a Church list.
///
/// NIL := FALSE
pub fn nil() -> Term { fls() }

/// Applied to a Church list it determines if it is empty.
///
/// NULL := λl.l (λhtd.FALSE) TRUE = λ 1 (λ λ λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::church::list::{nil, null};
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
/// use lambda_calculus::church::list::{nil, cons};
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
/// use lambda_calculus::church::list::head;
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
/// use lambda_calculus::church::list::tail;
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
/// use lambda_calculus::church::list::{length, nil};
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);
///
/// assert_eq!(beta(app(length(), nil()), NOR, 0, false), 0.into());
/// assert_eq!(beta(app(length(), list ), NOR, 0, false), 4.into());
/// ```
pub fn length() -> Term {
    app!(
        Z(),
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
/// use lambda_calculus::church::list::reverse;
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
        Z(),
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
/// use lambda_calculus::church::list::list;
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
/// use lambda_calculus::church::list::append;
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
    Z().app(
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
/// use lambda_calculus::church::list::index;
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
/// use lambda_calculus::church::list::map;
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
    Z().app(
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
/// use lambda_calculus::church::list::{foldl, nil};
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), list ), NOR, 0, false), 6.into());
/// assert_eq!(beta(app!(foldl(), plus(), 0.into(), nil()), NOR, 0, false), 0.into());
/// ```
pub fn foldl() -> Term {
    Z().app(
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
/// use lambda_calculus::church::list::{foldr, nil};
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
        Z(),
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
/// use lambda_calculus::church::list::{filter, nil};
/// use lambda_calculus::church::numerals::{is_zero, gt};
/// use lambda_calculus::combinators::C;
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let gt_1 = app!(C(), gt(), 1.into()); // greater than 1
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
    Z().app(
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
/// use lambda_calculus::church::list::{last};
/// use lambda_calculus::*;
///
/// let list = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
///
/// assert_eq!(beta(app(last(), list), NOR, 0, false), 3.into());
/// ```
pub fn last() -> Term {
    app(
        Z(),
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
/// use lambda_calculus::church::list::init;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let list2 = Term::from(vec![0.into(), 1.into(), 2.into()]);
///
/// assert_eq!(beta(app(init(), list1), NOR, 0, false), list2);
/// ```
pub fn init() -> Term {
    app(
        Z(),
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

/// Applied to two Church-encoded lists it returns a list of corresponding pairs. If one input list
/// is shorter, excess elements of the longer list are discarded.
///
/// ZIP := Z (λ.zab NULL b (λ.x NIL) (λ.x NULL a NIL (CONS (PAIR (HEAD b) (HEAD a)) (z (TAIL b) (TAIL a)))) I) =
/// Z (λ λ λ NULL 2 (λ NIL) (λ NULL 2 NIL (CONS (PAIR (HEAD 3) (HEAD 2)) (4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::list::zip;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![0.into(), 1.into()]);
/// let pairs1 = Term::from(vec![(0.into(), 0.into()).into(), (1.into(), 1.into()).into()]);
///
/// assert_eq!(beta(app!(zip(), list1.clone(), list1.clone()), NOR, 0, false), pairs1);
/// ```
pub fn zip() -> Term {
    app(
        Z(),
        abs!(3, app!(
            Var(2),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(2),
                abs!(5, Var(1)),
                abs!(2, Var(2)),
                abs!(2, Var(1)),
                abs(app!(
                    Var(1),
                    abs(app!(
                        Var(1),
                        app(Var(5), abs!(2, Var(2))),
                        app(Var(4), abs!(2, Var(2)))
                    )),
                    app!(
                        Var(5),
                        app(Var(4), abs!(2, Var(1))),
                        app(Var(3), abs!(2, Var(1)))
                    )
                ))
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a function and two Church-encoded lists it applies the function to the corresponding
/// elements and returns the resulting list. If one input list is shorter, excess elements of the
/// longer list are discarded.
///
/// ZIP_WITH := Z (λ.zfab NULL b (λ.x NIL) (λ.x NULL a NIL (CONS (f (HEAD b) (HEAD a)) (z f (TAIL b) (TAIL a)))) I) =
/// Z (λ λ λ λ NULL 2 (λ NIL) (λ NULL 2 NIL (CONS (4 (HEAD 3) (HEAD 2)) (5 4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::list::zip_with;
/// use lambda_calculus::church::numerals::plus;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![2.into(), 3.into()]);
/// let list2 = Term::from(vec![4.into(), 6.into()]);
///
/// assert_eq!(beta(app!(zip_with(), plus(), list1.clone(), list1), NOR, 0, false), list2);
/// ```
pub fn zip_with() -> Term {
    app(
        Z(),
        abs!(4, app!(
            Var(2),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(2),
                abs!(5, Var(1)),
                abs!(2, Var(2)),
                abs!(2, Var(1)),
                abs(app!(
                    Var(1),
                    app!(
                        Var(5),
                        app(Var(4), abs!(2, Var(2))),
                        app(Var(3), abs!(2, Var(2)))
                    ),
                    app!(
                        Var(6),
                        Var(5),
                        app(Var(4), abs!(2, Var(1))),
                        app(Var(3), abs!(2, Var(1)))
                    )
                ))
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a Church-encoded number `n` and a Church-encoded list it returns a new list with the
/// first `n` elements of the supplied list.
///
/// TAKE := Z (λznl. NULL l (λx.NIL) (λx.IS_ZERO n NIL (CONS (HEAD l) (z (PRED n) (TAIL l)))) I) =
/// Z (λ λ λ NULL l (λ NIL) (λ (IS_ZERO n NIL (CONS (HEAD l) (z (PRED n) (TAIL l))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::list::take;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![0.into(), 1.into(), 2.into(), 3.into()]);
/// let list2 = Term::from(vec![0.into(), 1.into()]);
///
/// assert_eq!(beta(app!(take(), 2.into(), list1), NOR, 0, false), list2);
pub fn take() -> Term {
    app(
        Z(),
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(2)),
            abs!(3, Var(1)),
            abs(app!(
                Var(3),
                abs!(3, Var(1)),
                abs!(2, Var(2)),
                abs!(2, Var(1)),
                abs(app!(
                    Var(1),
                    app(Var(3), abs!(2, Var(2))),
                    app!(
                        Var(5),
                        abs!(2, app!(
                            Var(6),
                            abs!(2, app(Var(1), app(Var(2), Var(4)))),
                            abs(Var(2)),
                            abs(Var(1))
                        )),
                        app(Var(3), abs!(2, Var(1)))
                    )
                ))
            )),
            abs(Var(1))
        ))
    )
}

/// Applied to a predicate function and a Church-encoded list it returns the longest prefix of the
/// list whose elements all satisfy the predicate function.
///
/// TAKE_WHILE := Z (λzfl. NULL l (λx.NIL) (λx.f (HEAD l) (CONS (HEAD l) (z f (TAIL l))) NIL) I) =
/// Z (λ λ λ NULL 1 (λ NIL) (λ 3 (HEAD 2) (CONS (HEAD 2) (4 3 (TAIL 2))) NIL) I)
///
/// # Example
/// ```
/// use lambda_calculus::church::list::take_while;
/// use lambda_calculus::church::numerals::is_zero;
/// use lambda_calculus::*;
///
/// let list1 = Term::from(vec![0.into(), 0.into(), 1.into()]);
/// let list2 = Term::from(vec![0.into(), 0.into()]);
///
/// assert_eq!(beta(app!(take_while(), is_zero(), list1), NOR, 0, false), list2);
/// ```
pub fn take_while() -> Term {
    app(
        Z(),
        abs!(3, app!(
            Var(1),
            abs!(5, Var(1)),
            abs!(2, Var(1)),
            abs!(3, Var(1)),
            abs(app!(
                Var(3),
                app(Var(2), abs!(2, Var(2))),
                abs(app!(
                    Var(1),
                    app(Var(3), abs!(2, Var(2))),
                    app!(Var(5), Var(4), app(Var(3), abs!(2, Var(1))))
                )),
                abs!(2, Var(1))
            )),
            abs(Var(1))
        ))
    )
}

impl From<Vec<Term>> for Term {
    fn from(terms: Vec<Term>) -> Self {
        let mut ret = nil();

        for term in terms.into_iter().rev() {
            ret = abs(app!(Var(1), term, ret))
        }

        ret
    }
}
