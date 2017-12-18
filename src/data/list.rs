//! [Lambda-encoded single-pair list](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use term::{Term, abs, app};
use term::Term::*;
use data::boolean::{tru, fls};
use data::pair::{pair, fst, snd};
use combinators::{I, Z};
use data::numerals::convert::Encoding;
use data::numerals::convert::Encoding::*;
use data::numerals::{church, scott, parigot, stumpfu};

/// Produces a `nil`, the last link of a lambda-encoded list; equivalent to `boolean::fls()`.
///
/// NIL := FALSE
pub fn nil() -> Term { fls() }

/// Applied to a lambda-encoded list it determines if it is empty.
///
/// IS_NIL := λl.l (λhtd.FALSE) TRUE = λ 1 (λ λ λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::list::is_nil;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_nil(), vec![].into()), NOR, 0), true.into());
/// ```
pub fn is_nil() -> Term {
    abs(app!(Var(1), abs!(3, fls()), tru()))
}

/// Applied to two terms it returns them contained in a lambda-encoded list; equivalent to `pair::pair()`.
///
/// CONS := PAIR
///
/// # Example
/// ```
/// use lambda_calculus::data::list::{nil, cons};
/// use lambda_calculus::*;
///
/// let list_consed =
///     app!(
///         cons(),
///         1.into_church(),
///         app!(
///             cons(),
///             2.into_church(),
///             app!(
///                 cons(),
///                 3.into_church(),
///                 nil()
///             )
///         )
///     );
///
/// let list_from_vec = vec![1, 2, 3].into_church();
///
/// assert_eq!(beta(list_consed, NOR, 0), list_from_vec);
/// ```
pub fn cons() -> Term { pair() }

/// Applied to a lambda-encoded list it returns its first element; equivalent to `pair::fst()`.
///
/// HEAD := FST
///
/// # Example
/// ```
/// use lambda_calculus::data::list::head;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_church();
///
/// assert_eq!(beta(app(head(), list), NOR, 0), 1.into_church());
/// ```
pub fn head() -> Term { fst() }

/// Applied to a lambda-encoded list it returns a new list with all its elements but the first one;
/// equivalent to `pair::snd()`.
///
/// TAIL := SND
///
/// # Example
/// ```
/// use lambda_calculus::data::list::tail;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_church();
///
/// assert_eq!(
///     beta(app(tail(), list), NOR, 0),
///     vec![2, 3].into_church()
/// );
/// ```
pub fn tail() -> Term { snd() }

/// Applied to a lambda-encoded list and a specific `Encoding` it returns its length in the given
/// encoding.
///
/// LENGTH := Z (λzal.IS_NIL l (λx.a) (λx.z (SUCC a) (SND l)) I) ZERO
/// = Z (λλλ IS_NIL 1 (λ 3) (λ 4 (SUCC 3) (SND 2)) I) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::list::{length, nil};
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(length(Church), nil()), NOR, 0),
///     0.into_church()
/// );
///
/// assert_eq!(
///     beta(app(length(Parigot), vec![1, 2, 3, 4].into_parigot()), NOR, 0),
///     4.into_parigot()
/// );
/// ```
pub fn length(encoding: Encoding) -> Term {
    let (succ, zero) = match encoding {
        Church =>  (church::succ(),  church::zero()),
        Scott =>   (scott::succ(),   scott::zero()),
        Parigot => (parigot::succ(), parigot::zero()),
        StumpFu => (stumpfu::succ(), stumpfu::zero())
    };

    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(Var(3)),
            abs(app!(
                Var(4),
                app(succ, Var(3)),
                app(snd(), Var(2))
            )),
            I()
        )),
        zero
    )
}

/// Applied to a number `i` with the given `Encoding` and a lambda-encoded list it returns the `i`-th
/// (zero-indexed) element of the list.
///
/// INDEX := λil. FST (l SND i) = λ λ FST (2 SND 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::index;
/// use lambda_calculus::*;
///
/// let list = || vec![1, 2, 3];
///
/// assert_eq!(
///     beta(app!(index(Church), 0.into_church(), list().into_church()), NOR, 0),
///     1.into_church()
/// );
/// ```
pub fn index(encoding: Encoding) -> Term {
    match encoding {
        Church => {
            abs!(2, app!(
                Var(2),
                abs(app(Var(1), abs!(2, Var(1)))),
                Var(1),
                abs!(2, Var(2))
            ))
        },
        _ => unimplemented!()
    }
}

/// Reverses a lambda-encoded list.
///
/// REVERSE := Z (λzal.IS_NIL l (λx.a) (λx.z (PAIR (FST l) a) (SND l) I)) NIL =
/// Z (λ λ λ IS_NIL 1 (λ 3) (λ 4 (PAIR (FST 2) 3) (SND 2)) I) NIL
///
/// # Example
/// ```
/// use lambda_calculus::data::list::reverse;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_church();
///
/// assert_eq!(
///     beta(app(reverse(), list), NOR, 0),
///     vec![3, 2, 1].into_church()
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

/// Applied to a lambda-encoded number `n` and `n` `Term`s it creates a lambda-encoded list of
/// those terms.
///
/// LIST := λn.n (λfax.f (PAIR x a)) REVERSE NIL = λ 1 (λ λ λ 3 (PAIR 1 2)) REVERSE NIL
///
/// # Example
/// ```
/// use lambda_calculus::data::list::list;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(list(), 3.into_church(), 1.into_church(), 2.into_church(), 3.into_church()), NOR, 0),
///     vec![1, 2, 3].into_church()
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

/// Applied to two lambda-encoded lists it concatenates them.
///
/// APPEND := Z (λzab. IS_NIL a (λx.b) (λx.PAIR (FST a) (z (SND a) b)) I) =
/// Z (λ λ λ IS_NIL 2 (λ 2) (λ PAIR (FST 3) (4 (SND 3) 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::append;
/// use lambda_calculus::*;
///
/// let list1 = vec![1, 2].into_church();
/// let list2 = vec![3, 4].into_church();
///
/// assert_eq!(
///     beta(app!(append(), list1, list2), NOR, 0),
///     vec![1, 2, 3, 4].into_church()
/// );
/// ```
pub fn append() -> Term {
    app(
        Z(),
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

/// Applied to a function and a lambda-encoded list it maps the function over it.
///
/// MAP := Z (λzfl. IS_NIL l (λx.NIL) (λx.PAIR (f (FST l)) (z f (SND l))) I) =
/// Z (λ λ λ IS_NIL 1 (λ NIL) (λ PAIR (3 (FST 2)) (4 3 (SND 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::map;
/// use lambda_calculus::data::numerals::church::succ;
/// use lambda_calculus::*;
///
/// let list = vec![1, 2, 3].into_church();
///
/// assert_eq!(
///     beta(app!(map(), succ(), list), NOR, 0),
///     vec![2, 3, 4].into_church()
/// );
/// ```
pub fn map() -> Term {
    app(
        Z(),
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

/// Applied to a function, a starting value and a lambda-encoded list it performs a
/// [left fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDL := Z (λzfsl. IS_NIL l (λx.s) (λx.z f (f s (FST l)) (SND l)) I) =
/// Z (λ λ λ λ IS_NIL 1 (λ 3) (λ 5 4 (4 3 (FST 2)) (SND 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::foldl;
/// use lambda_calculus::data::numerals::church::{add, sub};
/// use lambda_calculus::*;
///
/// let list = || vec![1, 2, 3].into_church();
///
/// assert_eq!(beta(app!(foldl(), add(), 0.into_church(), list()), NOR, 0), 6.into_church());
/// assert_eq!(beta(app!(foldl(), sub(), 6.into_church(), list()), NOR, 0), 0.into_church());
/// ```
pub fn foldl() -> Term {
    app(
        Z(),
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

/// Applied to a function, a starting value and a lambda-encoded list it performs a
/// [right fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDR := λfsl. Z (λzt. IS_NIL t (λx.s) (λx.f (FST t) (z (SND t))) I) l =
/// λ λ λ Z (λ λ IS_NIL 1 (λ 5) (λ 6 (FST 2) (3 (SND 2))) I) 1
///
/// # Example
/// ```
/// use lambda_calculus::data::list::foldr;
/// use lambda_calculus::data::numerals::church::{add, sub};
/// use lambda_calculus::*;
///
/// let list = || vec![1, 2, 3].into_church();
///
/// assert_eq!(beta(app!(foldr(), add(), 0.into_church(), list()), NOR, 0), 6.into_church());
/// assert_eq!(beta(app!(foldr(), sub(), 6.into_church(), list()), NOR, 0), 0.into_church());
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

/// Applied to a predicate and a lambda-encoded list it filters the list based on the predicate.
///
/// FILTER := Z (λzpl. IS_NIL l (λx.NIL) (λx.p (FST l) (PAIR (FST l)) I (z p (SND l))) I) =
/// Z (λ λ λ IS_NIL 1 (λ NIL) (λ 3 (FST 2) (PAIR (FST 2)) I (4 3 (SND 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::filter;
/// use lambda_calculus::data::numerals::church::{is_zero, gt};
/// use lambda_calculus::combinators::C;
/// use lambda_calculus::*;
///
/// let list = || vec![0, 1, 2, 3].into_church();
/// let gt_1 = app!(C(), gt(), 1.into_church()); // greater than 1
///
/// assert_eq!(
///     beta(app!(filter(), is_zero(), list()), NOR, 0),
///     vec![0].into_church()
/// );
/// assert_eq!(
///     beta(app!(filter(), gt_1, list()), NOR, 0),
///     vec![2, 3].into_church()
/// );
/// ```
pub fn filter() -> Term {
    app(
        Z(),
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

/// Applied to a lambda-encoded list it returns the last element.
///
/// LAST := Z (λzl.IS_NIL l (λx.NIL) (λx.IS_NIL (TAIL l) (HEAD l) (z (TAIL l))) I) =
/// Z (λ 2 1. IS_NIL 1 (λ NIL) (λ IS_NIL (TAIL 2) (HEAD 2) (3 (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::{last};
/// use lambda_calculus::*;
///
/// let list = vec![0, 1, 2, 3].into_church();
///
/// assert_eq!(beta(app(last(), list), NOR, 0), 3.into_church());
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

/// Applied to a lambda-encoded list it returns the list without the last element.
///
/// INIT := Z (λzl.IS_NIL l (λx.NIL) (λx.(IS_NIL (FST l) NIL (PAIR (FST l) (z (SND l))))) I) =
/// Z (λ λ IS_NIL 1 (λ NIL) (λ (IS_NIL (FST 2) NIL (PAIR (FST 2) (3 (SND 2))))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::init;
/// use lambda_calculus::*;
///
/// let list1 = vec![0, 1, 2, 3].into_church();
/// let list2 = vec![0, 1, 2].into_church();
///
/// assert_eq!(beta(app(init(), list1), NOR, 0), list2);
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

/// Applied to two lambda-encoded lists it returns a list of corresponding pairs. If one input list
/// is shorter, excess elements of the longer list are discarded.
///
/// ZIP := Z (λ.zab IS_NIL b (λ.x NIL) (λ.x IS_NIL a NIL (CONS (PAIR (HEAD b) (HEAD a)) (z (TAIL b) (TAIL a)))) I) =
/// Z (λ λ λ IS_NIL 2 (λ NIL) (λ IS_NIL 2 NIL (CONS (PAIR (HEAD 3) (HEAD 2)) (4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::zip;
/// use lambda_calculus::*;
///
/// let list  = || vec![0, 1].into_church();
/// let pairs = || vec![(0, 0), (1, 1)].into_church();
///
/// assert_eq!(beta(app!(zip(), list(), list()), NOR, 0), pairs());
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

/// Applied to a function and two lambda-encoded lists it applies the function to the corresponding
/// elements and returns the resulting list. If one input list is shorter, excess elements of the
/// longer list are discarded.
///
/// ZIP_WITH := Z (λ.zfab IS_NIL b (λ.x NIL) (λ.x IS_NIL a NIL (CONS (f (HEAD b) (HEAD a)) (z f (TAIL b) (TAIL a)))) I) =
/// Z (λ λ λ λ IS_NIL 2 (λ NIL) (λ IS_NIL 2 NIL (CONS (4 (HEAD 3) (HEAD 2)) (5 4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::zip_with;
/// use lambda_calculus::data::numerals::church::add;
/// use lambda_calculus::*;
///
/// let list1 = || vec![2, 3].into_church();
/// let list2 = || vec![4, 6].into_church();
///
/// assert_eq!(beta(app!(zip_with(), add(), list1(), list1()), NOR, 0), list2());
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

/// Applied to a number `n` with the specified `Encoding` and a lambda-encoded list it returns a new
/// list with the first `n` elements of the supplied list.
///
/// TAKE := Z (λznl.IS_NIL l (λx.NIL) (λx.IS_ZERO n NIL (CONS (HEAD l) (z (PRED n) (TAIL l)))) I) =
/// Z (λ λ λ IS_NIL 1 (λ NIL) (λ IS_ZERO 3 NIL (CONS (HEAD 2) (4 (PRED 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::take;
/// use lambda_calculus::*;
///
/// let list = || vec![1, 2, 3];
///
/// assert_eq!(
///     beta(app!(take(Church), 2.into_church(), list().into_church()), NOR, 0),
///     vec![1, 2].into_church()
/// );
/// assert_eq!(
///     beta(app!(take(Scott), 1.into_scott(), list().into_scott()), NOR, 0),
///     vec![1].into_scott()
/// );
/// ```
pub fn take(encoding: Encoding) -> Term {
    let (is_zero, pred) = match encoding {
        Church =>  (church::is_zero(),  church::pred()),
        Scott =>   (scott::is_zero(),   scott::pred()),
        Parigot => (parigot::is_zero(), parigot::pred()),
        StumpFu => (stumpfu::is_zero(), stumpfu::pred())
    };

    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(
                app!(
                    is_zero,
                    Var(3),
                    nil(),
                    app!(
                        cons(),
                        app(head(), Var(2)),
                        app!(
                            Var(4),
                            app(pred, Var(3)),
                            app(tail(), Var(2))
                        )
                    )
                )
            ),
            I()
        ))
    )
}

/// Applied to a predicate function and a lambda-encoded list it returns the longest prefix of the
/// list whose elements all satisfy the predicate function.
///
/// TAKE_WHILE := Z (λzfl. IS_NIL l (λx.NIL) (λx.f (HEAD l) (CONS (HEAD l) (z f (TAIL l))) NIL) I) =
/// Z (λ λ λ IS_NIL 1 (λ NIL) (λ 3 (HEAD 2) (CONS (HEAD 2) (4 3 (TAIL 2))) NIL) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::take_while;
/// use lambda_calculus::data::numerals::church::is_zero;
/// use lambda_calculus::*;
///
/// let list1 = vec![0, 0, 1].into_church();
/// let list2 = vec![0, 0].into_church();
///
/// assert_eq!(beta(app!(take_while(), is_zero(), list1), NOR, 0), list2);
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

impl Into<Term> for Vec<Term> {
    fn into(self) -> Term {
        let mut ret = nil();

        for term in self.into_iter().rev() {
            ret = abs(app!(Var(1), term, ret))
        }

        ret
    }
}
