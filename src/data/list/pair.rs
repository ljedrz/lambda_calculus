//! [Single-pair list](https://en.wikipedia.org/wiki/Church_encoding#One_pair_as_a_list_node)

use crate::term::{Term, abs, app};
use crate::term::Term::*;
use crate::data::boolean::{tru, fls};
use crate::data::pair::{pair, fst, snd};
use crate::combinators::{I, Z};
use crate::data::num::church::{zero, is_zero, succ, pred};

/// Produces a `nil`, the last link of a pair-encoded list; equivalent to `boolean::fls`.
///
/// NIL ≡ λab.b ≡ λ λ 1 ≡ FALSE
pub fn nil() -> Term { fls() }

/// Applied to a pair-encoded list it determines if it is empty.
///
/// IS_NIL ≡ λl.l (λhtd.FALSE) TRUE ≡ λ 1 (λ λ λ FALSE) TRUE
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::is_nil;
/// use lambda_calculus::*;
///
/// assert_eq!(beta(app(is_nil(),                vec![].into_pair_list()), NOR, 0),  true.into());
/// assert_eq!(beta(app(is_nil(), vec![1.into_church()].into_pair_list()), NOR, 0), false.into());
/// ```
pub fn is_nil() -> Term {
    abs(app!(Var(1), abs!(3, fls()), tru()))
}

/// Applied to two terms it returns them contained in a pair-encoded list; equivalent to `pair::pair`.
///
/// CONS ≡ λxyz.z x y ≡ λ λ λ 1 3 2 ≡ PAIR
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::{nil, cons};
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
/// let list_from_vec = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(beta(list_consed, NOR, 0), list_from_vec);
/// ```
pub fn cons() -> Term { pair() }

/// Applied to a pair-encoded list it returns its first element; equivalent to `pair::fst`.
///
/// HEAD ≡ λp.p TRUE ≡ λ 1 TRUE ≡ FST
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::head;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(beta(app(head(), list), NOR, 0), 1.into_church());
/// ```
pub fn head() -> Term { fst() }

/// Applied to a pair-encoded list it returns a new list with all its elements but the first one;
/// equivalent to `pair::snd`.
///
/// TAIL ≡ λp.p FALSE ≡ λ 1 FALSE ≡ SND
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::tail;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(
///     beta(app(tail(), list), NOR, 0),
///     vec![2.into_church(), 3.into_church()].into_pair_list()
/// );
/// ```
pub fn tail() -> Term { snd() }

/// Applied to a pair-encoded list it returns its Church-encoded length.
///
/// LENGTH ≡ Z (λzal.IS_NIL l (λx.a) (λx.z (SUCC a) (TAIL l)) I) ZERO
///        ≡ Z (λλλ IS_NIL 1 (λ 3) (λ 4 (SUCC 3) (TAIL 2)) I) ZERO
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::{length, nil};
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app(length(), nil()), NOR, 0),
///     0.into_church()
/// );
/// ```
pub fn length() -> Term {
    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(Var(3)),
            abs(app!(
                Var(4),
                app(succ(), Var(3)),
                app(tail(), Var(2))
            )),
            I()
        )),
        zero()
    )
}

/// Applied to a Church-encoded number `i` and a pair-encoded list it returns the `i`-th
/// (zero-indexed) element of the list.
///
/// INDEX ≡ λil.HEAD (i TAIL l) ≡ λ λ HEAD (2 TAIL 1)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::index;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()];
///
/// assert_eq!(
///     beta(app!(index(), 0.into_church(), list.into_pair_list()), NOR, 0),
///     1.into_church()
/// );
/// ```
pub fn index() -> Term {
    abs!(2, app(
        head(),
        app!(
            Var(2),
            tail(),
            Var(1)
        )
    ))
}

/// Reverses a pair-encoded list.
///
/// REVERSE ≡ Z (λzal.IS_NIL l (λx.a) (λx.z (CONS (HEAD l) a) (TAIL l) I)) NIL
///         ≡ Z (λ λ λ IS_NIL 1 (λ 3) (λ 4 (CONS (HEAD 2) 3) (TAIL 2)) I) NIL
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::reverse;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(
///     beta(app(reverse(), list), NOR, 0),
///     vec![3.into_church(), 2.into_church(), 1.into_church()].into_pair_list()
/// );
/// ```
pub fn reverse() -> Term {
    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(Var(3)),
            abs(app!(
                Var(4),
                app!(
                    cons(),
                    app(head(), Var(2)),
                    Var(3)
                ),
                app(tail(), Var(2))
            )),
            I()
        )),
        nil()
    )
}

/// Applied to a Church-encoded number `n` and `n` `Term`s it creates a pair-encoded list of those
/// terms.
///
/// LIST ≡ λn.n (λfax.f (CONS x a)) REVERSE NIL ≡ λ 1 (λ λ λ 3 (CONS 1 2)) REVERSE NIL
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::list;
/// use lambda_calculus::*;
///
/// assert_eq!(
///     beta(app!(list(), 3.into_church(), 1.into_church(), 2.into_church(), 3.into_church()), NOR, 0),
///     vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list()
/// );
/// ```
pub fn list() -> Term {
    abs(app!(
        Var(1),
        abs!(3, app(Var(3), app!(cons(), Var(1), Var(2)))),
        reverse(),
        nil()
    ))
}

/// Applied to two pair-encoded lists it concatenates them.
///
/// APPEND ≡ Z (λzab.IS_NIL a (λx.b) (λx.CONS (HEAD a) (z (TAIL a) b)) I)
///        ≡ Z (λ λ λ IS_NIL 2 (λ 2) (λ CONS (HEAD 3) (4 (TAIL 3) 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::append;
/// use lambda_calculus::*;
///
/// let list1 = vec![1.into_church(), 2.into_church()].into_pair_list();
/// let list2 = vec![3.into_church(), 4.into_church()].into_pair_list();
///
/// assert_eq!(
///     beta(app!(append(), list1, list2), NOR, 0),
///     vec![1.into_church(), 2.into_church(), 3.into_church(), 4.into_church()].into_pair_list()
/// );
/// ```
pub fn append() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(2),
            abs(Var(2)),
            abs(app!(
                cons(),
                app(head(), Var(3)),
                app!(
                    Var(4),
                    app(tail(), Var(3)),
                    Var(2)
                )
            )),
            I()
        ))
    )
}

/// Applied to a function and a pair-encoded list it maps the function over it.
///
/// MAP ≡ Z (λzfl.IS_NIL l (λx.NIL) (λx.CONS (f (HEAD l)) (z f (TAIL l))) I)
///     ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ CONS (3 (HEAD 2)) (4 3 (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::map;
/// use lambda_calculus::data::num::church::succ;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(
///     beta(app!(map(), succ(), list), NOR, 0),
///     vec![2.into_church(), 3.into_church(), 4.into_church()].into_pair_list()
/// );
/// ```
pub fn map() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                cons(),
                app(
                    Var(3),
                    app(head(), Var(2))
                ),
                app!(
                    Var(4),
                    Var(3),
                    app(tail(), Var(2))
                )
            )),
            I()
        ))
    )
}

/// Applied to a function, a starting value and a pair-encoded list it performs a
/// [left fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDL ≡ Z (λzfsl.IS_NIL l (λx.s) (λx.z f (f s (HEAD l)) (TAIL l)) I)
///       ≡ Z (λ λ λ λ IS_NIL 1 (λ 3) (λ 5 4 (4 3 (HEAD 2)) (TAIL 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::foldl;
/// use lambda_calculus::data::num::church::{add, sub};
/// use lambda_calculus::*;
///
/// let list = || vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(foldl(), add(), 0.into_church(), list()), NOR, 0), 6.into_church());
/// assert_eq!(beta(app!(foldl(), sub(), 6.into_church(), list()), NOR, 0), 0.into_church());
/// ```
pub fn foldl() -> Term {
    app(
        Z(),
        abs!(4, app!(
            is_nil(),
            Var(1),
            abs(Var(3)),
            abs(app!(
                Var(5),
                Var(4),
                app!(
                    Var(4),
                    Var(3),
                    app(head(), Var(2))
                ),
                app(tail(), Var(2))
            )),
            I()
        ))
    )
}

/// Applied to a function, a starting value and a pair-encoded list it performs a
/// [right fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)#Folds_on_lists)
/// on the list.
///
/// FOLDR ≡ λfal.Z (λzt.IS_NIL t (λx.a) (λx.f (HEAD t) (z (TAIL t))) I) l
///       ≡ λ λ λ Z (λ λ IS_NIL 1 (λ 5) (λ 6 (HEAD 2) (3 (TAIL 2))) I) 1
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::foldr;
/// use lambda_calculus::data::num::church::{add, sub};
/// use lambda_calculus::*;
///
/// let list = || vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(foldr(), add(), 0.into_church(), list()), NOR, 0), 6.into_church());
/// assert_eq!(beta(app!(foldr(), sub(), 6.into_church(), list()), NOR, 0), 0.into_church());
/// ```
pub fn foldr() -> Term {
    abs!(3, app!(
        Z(),
        abs!(2, app!(
            is_nil(),
            Var(1),
            abs(Var(5)),
            abs(app!(
                Var(6),
                app(head(), Var(2)),
                app!(
                    Var(3),
                    app(tail(), Var(2))
                )
            )),
            I()
        )),
        Var(1)
    ))
}

/// Applied to a predicate and a pair-encoded list it filters the list based on the predicate.
///
/// FILTER ≡ Z (λzpl.IS_NIL l (λx.NIL) (λx.p (HEAD l) (CONS (HEAD l)) I (z p (TAIL l))) I)
///        ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ 3 (HEAD 2) (CONS (HEAD 2)) I (4 3 (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::filter;
/// use lambda_calculus::data::num::church::{is_zero, gt};
/// use lambda_calculus::combinators::C;
/// use lambda_calculus::*;
///
/// let list = || vec![0.into_church(), 1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
/// let gt_1 = app!(C(), gt(), 1.into_church()); // greater than 1
///
/// assert_eq!(
///     beta(app!(filter(), is_zero(), list()), NOR, 0),
///     vec![0.into_church()].into_pair_list()
/// );
/// assert_eq!(
///     beta(app!(filter(), gt_1, list()), NOR, 0),
///     vec![2.into_church(), 3.into_church()].into_pair_list()
/// );
/// ```
pub fn filter() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
             Var(3),
                app(head(), Var(2)),
                app(cons(), app(head(), Var(2))),
                I(),
                app!(Var(4), Var(3), app(tail(), Var(2)))
            )),
            I()
        ))
    )
}

/// Applied to a pair-encoded list it returns the last element.
///
/// LAST ≡ Z (λzl.IS_NIL l (λx.NIL) (λx.IS_NIL (TAIL l) (HEAD l) (z (TAIL l))) I)
///      ≡ Z (λ λ IS_NIL 1 (λ NIL) (λ IS_NIL (TAIL 2) (HEAD 2) (3 (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::last;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
///
/// assert_eq!(beta(app(last(), list), NOR, 0), 3.into_church());
/// ```
pub fn last() -> Term {
    app(
        Z(),
        abs!(2, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                is_nil(),
                app(tail(), Var(2)),
                app(head(), Var(2)),
                app(
                    Var(3),
                    app(tail(), Var(2))
                )
            )),
            I()
        ))
    )
}

/// Applied to a pair-encoded list it returns the list without the last element.
///
/// INIT ≡ Z (λzl.IS_NIL l (λx.NIL) (λx.IS_NIL (TAIL l) NIL (CONS (HEAD l) (z (TAIL l)))) I)
///      ≡ Z (λ λ IS_NIL 1 (λ NIL) (λ IS_NIL (TAIL 2) NIL (CONS (HEAD 2) (3 (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::init;
/// use lambda_calculus::*;
///
/// let list1 = vec![1.into_church(), 2.into_church(), 3.into_church()].into_pair_list();
/// let list2 = vec![1.into_church(), 2.into_church()].into_pair_list();
///
/// assert_eq!(beta(app(init(), list1), NOR, 0), list2);
/// ```
pub fn init() -> Term {
    app(
        Z(),
        abs!(2, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                is_nil(),
                app(tail(), Var(2)),
                nil(),
                app!(
                    cons(),
                    app(head(), Var(2)),
                    app(
                        Var(3),
                        app(tail(), Var(2))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to two pair-encoded lists it returns a list of corresponding pairs. If one input list
/// is shorter, excess elements of the longer list are discarded.
///
/// ZIP ≡ Z (λzab.IS_NIL b (λx.NIL) (λx.IS_NIL a NIL (CONS (CONS (HEAD b) (HEAD a)) (z (TAIL b) (TAIL a)))) I)
///     ≡ Z (λ λ λ IS_NIL 2 (λ NIL) (λ IS_NIL 2 NIL (CONS (CONS (HEAD 3) (HEAD 2)) (4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::zip;
/// use lambda_calculus::*;
///
/// let list  = || vec![0.into_church(), 1.into_church()].into_pair_list();
/// let pairs = || vec![(0, 0).into_church(), (1, 1).into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(zip(), list(), list()), NOR, 0), pairs());
/// ```
pub fn zip() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(2),
            abs(nil()),
            abs(app!(
                is_nil(),
                Var(2),
                nil(),
                app!(
                    cons(),
                    app!(
                        cons(),
                        app(head(), Var(3)),
                        app(head(), Var(2))
                    ),
                    app!(
                        Var(4),
                        app(tail(), Var(3)),
                        app(tail(), Var(2))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to a function and two pair-encoded lists it applies the function to the corresponding
/// elements and returns the resulting list. If one input list is shorter, excess elements of the
/// longer list are discarded.
///
/// ZIP_WITH ≡ Z (λzfab.IS_NIL b (λx.NIL) (λx.IS_NIL a NIL (CONS (f (HEAD b) (HEAD a)) (z f (TAIL b) (TAIL a)))) I)
///          ≡ Z (λ λ λ λ IS_NIL 2 (λ NIL) (λ IS_NIL 2 NIL (CONS (4 (HEAD 3) (HEAD 2)) (5 4 (TAIL 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::zip_with;
/// use lambda_calculus::data::num::church::add;
/// use lambda_calculus::*;
///
/// let list1 = || vec![2.into_church(), 3.into_church()].into_pair_list();
/// let list2 = || vec![4.into_church(), 6.into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(zip_with(), add(), list1(), list1()), NOR, 0), list2());
/// ```
pub fn zip_with() -> Term {
    app(
        Z(),
        abs!(4, app!(
            is_nil(),
            Var(2),
            abs(nil()),
            abs(app!(
                is_nil(),
                Var(2),
                nil(),
                app!(
                    cons(),
                    app!(
                        Var(4),
                        app(head(), Var(3)),
                        app(head(), Var(2))
                    ),
                    app!(
                        Var(5),
                        Var(4),
                        app(tail(), Var(3)),
                        app(tail(), Var(2))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to a Church-encoded number `n` and a pair-encoded list it returns a new list with the
/// first `n` elements of the supplied list.
///
/// TAKE ≡ Z (λznl.IS_NIL l (λx.NIL) (λx.IS_ZERO n NIL (CONS (HEAD l) (z (PRED n) (TAIL l)))) I)
///      ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ IS_ZERO 3 NIL (CONS (HEAD 2) (4 (PRED 3) (TAIL 2)))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::take;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()];
///
/// assert_eq!(
///     beta(app!(take(), 2.into_church(), list.into_pair_list()), NOR, 0),
///     vec![1.into_church(), 2.into_church()].into_pair_list()
/// );
/// ```
pub fn take() -> Term {
    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                is_zero(),
                Var(3),
                nil(),
                app!(
                    cons(),
                    app(head(), Var(2)),
                    app!(
                        Var(4),
                        app(pred(), Var(3)),
                        app(tail(), Var(2))
                    )
                )
            )),
            I()
        ))
    )
}

/// Applied to a predicate function and a pair-encoded list it returns the longest prefix of the
/// list whose elements all satisfy the predicate function.
///
/// TAKE_WHILE ≡ Z (λzfl. IS_NIL l (λx.NIL) (λx.f (HEAD l) (CONS (HEAD l) (z f (TAIL l))) NIL) I)
///            ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ 3 (HEAD 2) (CONS (HEAD 2) (4 3 (TAIL 2))) NIL) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::take_while;
/// use lambda_calculus::data::num::church::is_zero;
/// use lambda_calculus::*;
///
/// let list1 = vec![0.into_church(), 0.into_church(), 1.into_church()].into_pair_list();
/// let list2 = vec![0.into_church(), 0.into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(take_while(), is_zero(), list1), NOR, 0), list2);
/// ```
pub fn take_while() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                Var(3),
                app(head(), Var(2)),
                app!(
                    cons(),
                    app(head(), Var(2)),
                    app!(
                        Var(4),
                        Var(3),
                        app(tail(), Var(2))
                    )
                ),
                nil()
            )),
            I()
        ))
    )
}

/// Applied to a Church-encoded number `n` and a pair-encoded list it returns a new list without
/// the first `n` elements of the supplied list.
///
/// DROP ≡ Z (λznl.IS_NIL l (λx.NIL) (λx.IS_ZERO n l (z (PRED n) (TAIL l))) I)
///      ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ IS_ZERO 3 2 (4 (PRED 3) (TAIL 2))) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::drop;
/// use lambda_calculus::*;
///
/// let list = vec![1.into_church(), 2.into_church(), 3.into_church()];
///
/// assert_eq!(
///     beta(app!(drop(), 1.into_church(), list.into_pair_list()), NOR, 0),
///     vec![2.into_church(), 3.into_church()].into_pair_list()
/// );
/// ```
pub fn drop() -> Term {
    app!(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                is_zero(),
                Var(3),
                Var(2),
                app!(
                    Var(4),
                    app(pred(), Var(3)),
                    app(tail(), Var(2))
                )
            )),
            I()
        ))
    )
}

/// Applied to a predicate function and a pair-encoded list it returns a new list without
/// the prefix of the supplied list whose elements satisfy the predicate function.
///
/// DROP_WHILE ≡ Z (λzfl.IS_NIL l (λx.NIL) (λx.f (HEAD l) (z f (TAIL l)) l) I)
///            ≡ Z (λ λ λ IS_NIL 1 (λ NIL) (λ 3 (HEAD 2) (4 3 (TAIL 2)) 2) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::drop_while;
/// use lambda_calculus::data::num::church::is_zero;
/// use lambda_calculus::*;
///
/// let list1 = vec![0.into_church(), 0.into_church(), 1.into_church(), 0.into_church()].into_pair_list();
/// let list2 = vec![1.into_church(), 0.into_church()].into_pair_list();
///
/// assert_eq!(beta(app!(drop_while(), is_zero(), list1), NOR, 0), list2);
/// ```
pub fn drop_while() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_nil(),
            Var(1),
            abs(nil()),
            abs(app!(
                Var(3),
                app(head(), Var(2)),
                app!(
                    Var(4),
                    Var(3),
                    app(tail(), Var(2))
                ),
                Var(2)
            )),
            I()
        ))
    )
}

/// Applied to a Church-encoded number `n` and an argument, it produces a list containing the
/// argument repeated `n` times.
///
/// REPLICATE ≡ Z (λzny.IS_ZERO n (λx.NIL) (λx.PAIR y (z (PRED n) y)) I)
///           ≡ Z (λ λ λ IS_ZERO 2 (λ NIL) (λ PAIR 2 (4 (PRED 3) 2)) I)
///
/// # Example
/// ```
/// use lambda_calculus::data::list::pair::replicate;
/// use lambda_calculus::*;
///
/// let list1 = vec![2.into_church(), 2.into_church(), 2.into_church()].into_pair_list();
/// let list2 = vec![].into_pair_list();
///
/// assert_eq!(beta(app!(replicate(), 3.into_church(), 2.into_church()), NOR, 0), list1);
/// assert_eq!(beta(app!(replicate(), 0.into_church(), 4.into_church()), NOR, 0), list2);
/// ```
pub fn replicate() -> Term {
    app(
        Z(),
        abs!(3, app!(
            is_zero(),
            Var(2),
            abs(nil()),
            abs(app!(
                pair(),
                Var(2),
                app!(
                    Var(4),
                    app(pred(), Var(3)),
                    Var(2)
                )
            )),
            I()
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
