//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use term::{Term, TermError};
use term::Term::*;
use std::fmt;
use std::mem;
pub use self::Order::*;

/// The [evaluation order](http://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf) of
/// β-reductions. The default is `NOR` (normal order).
///
/// They don't always yield the same result:
///
/// - The `NOR`, `HNO`, `APP` and `HAP` orders reduce expressions to their normal forms
/// - The `APP` order will fail to fully reduce expressions containing functions without a normal
/// form, e.g. the `Y` combinator (they will expand forever)
/// - The `CBN` order reduces to weak head normal form
/// - The `CBV` order reduces to weak normal form
/// - The `HSP` order reduces to head normal form
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Order {
    /// Normal - leftmost outermost; the most popular lambda calculus reduction strategy
    NOR,
    /// Call-by-name - leftmost outermost, but no reductions inside abstractions
    CBN,
    /// Head spine - leftmost outermost, but abstractions reduced only in head position
    HSP,
    /// Hybrid normal - a hybrid between `HSP` (head spine) and `NOR` (normal) strategies
    HNO,
    /// Applicative - leftmost innermost; the most eager strategy; unfit for recursion combinators
    APP,
    /// Call-by-value - leftmost innermost, but no reductions inside abstractions
    CBV,
    /// Hybrid applicative - a hybrid between `CBV` (call-by-value) and `APP` (applicative)
    /// strategies; usually the fastest-reducing normalizing strategy
    HAP
}

/// Applies two `Term`s with substitution and variable update, consuming the first one in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::reduction::apply;
/// use lambda_calculus::*;
///
/// // these are valid terms, but be careful with unwraps in your code
/// let lhs    = parse(&"λλ42(λ13)", DeBruijn).unwrap();
/// let rhs    = parse(&"λ51", DeBruijn).unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))", DeBruijn).unwrap();
///
/// assert_eq!(apply(lhs, &rhs), Ok(result));
/// ```
/// # Errors
///
/// The function will return an error if the `lhs` term is not an `Abs`traction.
pub fn apply(mut lhs: Term, rhs: &Term) -> Result<Term, TermError> {
    lhs.unabs_ref()?;

    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: &Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs.to_owned(); // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(ref mut abstracted) => {
            _apply(abstracted, rhs, depth + 1)
        },
        App(ref mut lhs_lhs, ref mut lhs_rhs) => {
            _apply(lhs_lhs, rhs, depth);
            _apply(lhs_rhs, rhs, depth)
        }
    }
}

fn update_free_variables(term: &mut Term, added_depth: usize, own_depth: usize) {
    match *term {
        Var(ref mut i) => if *i > own_depth {
            *i += added_depth
        },
        Abs(ref mut abstracted) => {
            update_free_variables(abstracted, added_depth, own_depth + 1)
        },
        App(ref mut lhs, ref mut rhs) => {
            update_free_variables(lhs, added_depth, own_depth);
            update_free_variables(rhs, added_depth, own_depth)
        }
    }
}

/// Performs β-reduction on a `Term` with the specified evaluation `Order` and an optional limit on
/// the number of reductions (`0` means no limit) and returns the reduced `Term`.
///
/// # Example
///
/// ```
/// use lambda_calculus::*;
///
/// let expr    = parse(&"(λa.λb.λc.a (λd.λe.e (d b)) (λd.c) (λd.d)) (λa.λb.a b)", Classic).unwrap();
/// let reduced = parse(&"λa.λb.b", Classic).unwrap();
///
/// assert_eq!(beta(expr, NOR, 0), reduced);
/// ```
pub fn beta(mut term: Term, order: Order, limit: usize) -> Term {
    term.reduce(order, limit);
    term
}

/// Performs β-reduction on a `Term` with the specified evaluation `Order` and an optional limit
/// on the number of reductions (`0` means no limit) and returns a vector with all the states
/// of the `Term` during the reduction process.
///
/// # Example
///
/// ```
/// use lambda_calculus::*;
///
/// let mut expr = parse(&"(λa.λb.λc.b (a b c)) (λa.λb.b)", Classic).unwrap();
/// let reduction_stages = beta_verbose(expr, NOR, 0);
///
/// assert_eq!(
///     reduction_stages,
///     vec![
///         parse(&"(λa.λb.λc.b (a b c)) (λa.λb.b)", Classic).unwrap(),
///         parse(&"λa.λb.a ((λc.λd.d) a b)",        Classic).unwrap(),
///         parse(&"λa.λb.a ((λc.c) b)",             Classic).unwrap(),
///         parse(&"λa.λb.a b",                      Classic).unwrap()
///     ]
/// );
/// ```
pub fn beta_verbose(mut term: Term, order: Order, limit: usize) -> Vec<Term> {
    let mut count = 0;
    let mut ret = Vec::new();
    let limit = if limit == 0 {
        usize::max_value() // this should always suffice
    } else {
        limit + 1 // +1 for the range to be inclusive
    };

    ret.push(term.clone());

    for l in 1..limit {
        match order {
            CBN => term.beta_cbn(l, &mut count),
            NOR => term.beta_nor(l, &mut count),
            CBV => term.beta_cbv(l, &mut count),
            APP => term.beta_app(l, &mut count),
            HSP => term.beta_hsp(l, &mut count),
            HNO => term.beta_hno(l, &mut count),
            HAP => term.beta_hap(l, &mut count)
        }

        if term != *ret.last().unwrap() { // safe, always non-empty
            ret.push(term.clone());
        } else {
            break
        }
    }

    ret
}

/// For a given `Term` and a set of β-reduction `Order`s it returns a vector of pairs containing
/// the `Order`s and their corresponding numbers of reductions required for the `Term` to reach its
/// fully reduced form (which, depending on the reduction strategy, might not be the normal form).
///
/// # Example
///
/// ```
/// use lambda_calculus::reduction::compare;
/// use lambda_calculus::*;
///
/// let factorial_3 = parse(&"(λa.a (λb.λc.λd.b (λe.c (d e)) (λe.λf.e (d e f))) (λb.λc.b)\
///     (λb.λc.b c) (λb.λc.b c)) (λa.λb.a (a (a b)))", Classic).unwrap();
///
/// assert_eq!(
///     compare(&factorial_3, &[NOR, APP, HNO, HAP]),
///     vec![(NOR, 35), (APP, 36), (HNO, 35), (HAP, 30)]
/// );
/// ```
pub fn compare(term: &Term, orders: &[Order]) -> Vec<(Order, usize)> {
    let mut ret = Vec::with_capacity(orders.len());

    for order in orders {
        ret.push((order.to_owned(), term.to_owned().reduce(*order, 0)));
    }

    ret
}

impl Term {
    /// Reduces an `App`lication by substitution and variable update.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    /// use lambda_calculus::combinators::I;
    ///
    /// assert_eq!(app(I(), Var(1)).eval(), Ok(Var(1)));
    /// ```
    /// # Errors
    ///
    /// The function will return an error if `self` is not an `App`lication or if its left hand
    /// side term is not an `Abs`traction.
    pub fn eval(self) -> Result<Term, TermError> {
        let (lhs, rhs) = self.unapp()?;

        apply(lhs, &rhs)
    }

    fn _eval(&mut self, count: &mut usize) {
        let mut to_eval = mem::replace(self, Var(0)); // replace self with a dummy
        to_eval = to_eval.eval().unwrap(); // safe; only called in reduction sites
        mem::replace(self, to_eval); // move self back to its place

        *count += 1;
    }

    fn is_reducible(&self, limit: usize, count: &usize) -> bool {
        self.lhs_ref().and_then(|t| t.unabs_ref()).is_ok() && (limit == 0 || *count < limit )
    }

    /// Performs β-reduction on a `Term` with the specified evaluation `Order` and an optional limit
    /// on the number of reductions (`0` means no limit) and returns the number of performed
    /// reductions.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let mut expression = parse(&"(λa.λb.λc.b (a b c)) (λa.λb.b)", Classic).unwrap();
    /// let reduced        = parse(&"λa.λb.a b", Classic).unwrap();
    ///
    /// expression.reduce(NOR, 0);
    ///
    /// assert_eq!(expression, reduced);
    /// ```
    pub fn reduce(&mut self, order: Order, limit: usize) -> usize {
        let mut count = 0;

        match order {
            CBN => self.beta_cbn(limit, &mut count),
            NOR => self.beta_nor(limit, &mut count),
            CBV => self.beta_cbv(limit, &mut count),
            APP => self.beta_app(limit, &mut count),
            HSP => self.beta_hsp(limit, &mut count),
            HNO => self.beta_hno(limit, &mut count),
            HAP => self.beta_hap(limit, &mut count)
        }

        count
    }

    fn beta_cbn(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        if let App(_, _) = *self {
            self.lhs_mut().unwrap().beta_cbn(limit, count);

            if self.is_reducible(limit, count) {
                self._eval(count);
                self.beta_cbn(limit, count);
            }
        }
    }

    fn beta_nor(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_nor(limit, count),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_cbn(limit, count);

                if self.is_reducible(limit, count) {
                    self._eval(count);
                    self.beta_nor(limit, count);
                } else {
                    self.lhs_mut().unwrap().beta_nor(limit, count);
                    self.rhs_mut().unwrap().beta_nor(limit, count);
                }
            },
            _ => ()
        }
    }

    fn beta_cbv(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        if let App(_, _) = *self {
            self.lhs_mut().unwrap().beta_cbv(limit, count);
            self.rhs_mut().unwrap().beta_cbv(limit, count);

            if self.is_reducible(limit, count) {
                self._eval(count);
                self.beta_cbv(limit, count);
            }
        }
    }

    fn beta_app(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_app(limit, count),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_app(limit, count);
                self.rhs_mut().unwrap().beta_app(limit, count);

                if self.is_reducible(limit, count) {
                    self._eval(count);
                    self.beta_app(limit, count);
                }
            },
            _ => ()
        }
    }

    fn beta_hap(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hap(limit, count),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_cbv(limit, count);
                self.rhs_mut().unwrap().beta_hap(limit, count);

                if self.is_reducible(limit, count) {
                    self._eval(count);
                    self.beta_hap(limit, count);
                } else {
                    self.lhs_mut().unwrap().beta_hap(limit, count);
                }
            },
            _ => ()
        }
    }

    fn beta_hsp(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hsp(limit, count),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_hsp(limit, count);

                if self.is_reducible(limit, count) {
                    self._eval(count);
                    self.beta_hsp(limit, count)
                }
            },
            _ => ()
        }
    }

    fn beta_hno(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_hno(limit, count),
            App(_, _) => {
                self.lhs_mut().unwrap().beta_hsp(limit, count);

                if self.is_reducible(limit, count) {
                    self._eval(count);
                    self.beta_hno(limit, count)
                } else {
                    self.lhs_mut().unwrap().beta_hno(limit, count);
                    self.rhs_mut().unwrap().beta_hno(limit, count);
                }
            },
            _ => ()
        }
    }
}

impl fmt::Display for Order {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match *self {
            NOR => "normal",
            CBN => "call-by-name",
            HSP => "head spine",
            HNO => "hybrid normal",
            APP => "applicative",
            CBV => "call-by-value",
            HAP => "hybrid applicative"
        })
    }
}
