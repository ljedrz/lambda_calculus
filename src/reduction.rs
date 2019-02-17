//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use crate::term::{Term, TermError};
use crate::term::Term::*;
use std::fmt;
use std::mem;
pub use self::Order::*;

/// The [evaluation order](http://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf) of
/// β-reductions.
///
/// - the `NOR`, `HNO`, `APP` and `HAP` orders reduce expressions to their normal form
/// - the `APP` order will fail to fully reduce expressions containing terms without a normal form,
/// e.g. the `Y` combinator (they will expand forever)
/// - the `CBN` order reduces to weak head normal form
/// - the `CBV` order reduces to weak normal form
/// - the `HSP` order reduces to head normal form
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Order {
    /// normal - leftmost outermost; the most popular reduction strategy
    NOR,
    /// call-by-name - leftmost outermost, no reductions inside abstractions
    CBN,
    /// head spine - leftmost outermost, abstractions reduced only in head position
    HSP,
    /// hybrid normal - a mix between `HSP` (head spine) and `NOR` (normal) strategies
    HNO,
    /// applicative - leftmost innermost; the most eager strategy; unfit for recursion combinators
    APP,
    /// call-by-value - leftmost innermost, no reductions inside abstractions
    CBV,
    /// hybrid applicative - a mix between `CBV` (call-by-value) and `APP` (applicative) strategies;
    /// usually the fastest-reducing normalizing strategy
    HAP
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

impl Term {
    /// Applies a `Term` to `self` via substitution and variable update.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::*;
    ///
    /// let mut term1  = parse(&"λλ42(λ13)", DeBruijn).unwrap();
    /// let term2      = parse(&"λ51", DeBruijn).unwrap();
    /// let result     = parse(&"λ3(λ61)(λ1(λ71))", DeBruijn).unwrap();
    ///
    /// term1.apply(&term2);
    ///
    /// assert_eq!(term1, result);
    /// ```
    /// # Errors
    ///
    /// Returns a `TermError` if `self` is not an `Abs`traction.
    pub fn apply(&mut self, rhs: &Term) -> Result<(), TermError> {
        self.unabs_ref()?;

        self._apply(rhs, 0);

        let ret = mem::replace(self, Var(0)); // replace self with a dummy
        mem::replace(self, ret.unabs().unwrap()); // move unabstracted self back to its place

        Ok(())
    }

    fn _apply(&mut self, rhs: &Term, depth: usize) {
        match self {
            Var(i) => if *i == depth {
                *self = rhs.to_owned(); // substitute a top-level variable from lhs with rhs
                self.update_free_variables(depth - 1, 0); // update indices of free variables from rhs
            } else if *i > depth {
                *self = Var(*i - 1) // decrement a free variable's index
            },
            Abs(ref mut abstracted) => {
                abstracted._apply(rhs, depth + 1)
            },
            App(boxed) => {
                let (ref mut lhs_lhs, ref mut lhs_rhs) = **boxed;
                lhs_lhs._apply(rhs, depth);
                lhs_rhs._apply(rhs, depth)
            }
        }
    }

    fn update_free_variables(&mut self, added_depth: usize, own_depth: usize) {
        match self {
            Var(ref mut i) => if *i > own_depth {
                *i += added_depth
            },
            Abs(ref mut abstracted) => {
                abstracted.update_free_variables(added_depth, own_depth + 1)
            },
            App(boxed) => {
                let (ref mut lhs, ref mut rhs) = **boxed;
                lhs.update_free_variables(added_depth, own_depth);
                rhs.update_free_variables(added_depth, own_depth)
            }
        }
    }

    fn eval(&mut self, count: &mut usize) {
        let to_apply = mem::replace(self, Var(0)); // replace self with a dummy
        let (mut lhs, rhs) = to_apply.unapp().unwrap(); // safe; only called in reduction sites
        lhs.apply(&rhs).unwrap(); // ditto
        mem::replace(self, lhs); // move self back to its place

        *count += 1;
    }

    fn is_reducible(&self, limit: usize, count: usize) -> bool {
        self.lhs_ref().and_then(|t| t.unabs_ref()).is_ok() && (limit == 0 || count < limit )
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

        if let App(_) = *self {
            self.lhs_mut().unwrap().beta_cbn(limit, count);

            if self.is_reducible(limit, *count) {
                self.eval(count);
                self.beta_cbn(limit, count);
            }
        }
    }

    fn beta_nor(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_nor(limit, count),
            App(_) => {
                self.lhs_mut().unwrap().beta_cbn(limit, count);

                if self.is_reducible(limit, *count) {
                    self.eval(count);
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

        if let App(_) = *self {
            self.lhs_mut().unwrap().beta_cbv(limit, count);
            self.rhs_mut().unwrap().beta_cbv(limit, count);

            if self.is_reducible(limit, *count) {
                self.eval(count);
                self.beta_cbv(limit, count);
            }
        }
    }

    fn beta_app(&mut self, limit: usize, count: &mut usize) {
        if limit != 0 && *count == limit { return }

        match *self {
            Abs(ref mut abstracted) => abstracted.beta_app(limit, count),
            App(_) => {
                self.lhs_mut().unwrap().beta_app(limit, count);
                self.rhs_mut().unwrap().beta_app(limit, count);

                if self.is_reducible(limit, *count) {
                    self.eval(count);
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
            App(_) => {
                self.lhs_mut().unwrap().beta_cbv(limit, count);
                self.rhs_mut().unwrap().beta_hap(limit, count);

                if self.is_reducible(limit, *count) {
                    self.eval(count);
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
            App(_) => {
                self.lhs_mut().unwrap().beta_hsp(limit, count);

                if self.is_reducible(limit, *count) {
                    self.eval(count);
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
            App(_) => {
                self.lhs_mut().unwrap().beta_hsp(limit, count);

                if self.is_reducible(limit, *count) {
                    self.eval(count);
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
