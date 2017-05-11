//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use term::*;
use term::Term::*;
use self::Order::*;

/// Set to `true` to see all the steps of β-reductions. The default is `false`.
pub const SHOW_REDUCTIONS: bool = false;

/// The [evaluation order](https://en.wikipedia.org/wiki/Lambda_calculus#Reduction_strategies) of
/// β-reductions. `Applicative` order will fail to fully reduce expressions containing functions
/// without a normal form, e.g. the Y combinator (they will expand forever). The default is
/// `Normal`.
#[derive(Debug, PartialEq)]
pub enum Order {
    /// leftmost outermost
    Normal,
    /// leftmost outermost, but not inside abstractions
    CallByName,
    /// leftmost outermost, but abstractions reduced only in head position
    HeadSpine,
    /// `HeadSpine` + `Normal`
    HybridNormal,
    /// leftmost innermost
    Applicative,
    /// leftmost innermost, but not inside abstractions
    CallByValue,
    /// `CallByValue` + `Applicative`
    HybridApplicative
}

/// Applies two `Term`s with substitution and variable update, consuming the first one in the
/// process.
///
/// # Example
/// ```
/// use lambda_calculus::reduction::apply;
/// use lambda_calculus::parser::parse;
///
/// let lhs    = parse(&"λλ42(λ13)").unwrap();
/// let rhs    = parse(&"λ51").unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
///
/// assert_eq!(apply(lhs, &rhs), Ok(result));
/// ```
pub fn apply(mut lhs: Term, rhs: &Term) -> Result<Term, Error> {
    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: &Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs.clone(); // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(_) => {
            _apply(lhs.unabs_ref_mut().unwrap(), rhs, depth + 1)
        },
        App(_, _) => {
            _apply(lhs.lhs_ref_mut().unwrap(), rhs, depth);
            _apply(lhs.rhs_ref_mut().unwrap(), rhs, depth)
        }
    }
}

fn update_free_variables(term: &mut Term, added_depth: usize, own_depth: usize) {
    match *term {
        Var(i) => if i > own_depth {
            *term = Var(i + added_depth)
        },
        Abs(_) => {
            update_free_variables(term.unabs_ref_mut().unwrap(), added_depth, own_depth + 1)
        },
        App(_, _) => {
            update_free_variables(term.lhs_ref_mut().unwrap(), added_depth, own_depth);
            update_free_variables(term.rhs_ref_mut().unwrap(), added_depth, own_depth)
        }
    }
}

impl Term {
    /// Applies `self` to another `Term` and performs substitution, consuming `self` in the process.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::parser::parse;
    ///
    /// let lhs    = parse(&"λλ42(λ13)").unwrap();
    /// let rhs    = parse(&"λ51").unwrap();
    /// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
    ///
    /// assert_eq!(lhs.apply(&rhs), Ok(result));
    /// ```
    pub fn apply(self, rhs: &Term) -> Result<Term, Error> {
        apply(self, rhs)
    }

    /// Reduces an `App`lication by substitution and variable update.
    ///
    /// # Example
    /// ```
    /// use lambda_calculus::term::{app, abs};
    /// use lambda_calculus::term::Term::Var;
    /// use lambda_calculus::arithmetic::zero;
    /// use lambda_calculus::combinators::i;
    ///
    /// assert_eq!(app(i(), zero()).eval(), Ok(zero()));
    /// ```
    pub fn eval(self) -> Result<Term, Error> {
        let (lhs, rhs) = try!(self.unapp());

        apply(lhs, &rhs)
    }

    /// Performs a single β-reduction on `self` with the specified evaluation `Order`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::succ;
    /// use lambda_calculus::reduction::Order;
    ///
    /// let mut succ_one = succ().app(1.into());
    /// succ_one.beta_once(&Order::Normal);
    ///
    /// assert_eq!(succ_one, succ().apply(&1.into()).unwrap());
    /// ```
    pub fn beta_once(&mut self, order: &Order) {
        self.beta_once_indicative(order);
    }

    fn beta_once_indicative(&mut self, order: &Order) -> bool {
        match *order {
            Normal       => self._beta_once_normal(0),
            CallByName   => self._beta_once_call_by_name(),
            HeadSpine    => self._beta_once_head_spine(0, true),
            Applicative  => self._beta_once_applicative(0),
            CallByValue  => self._beta_once_call_by_value(),
            HybridNormal => {
                self._beta_once_head_spine(0, true);
                self._beta_once_normal(0)
            },
            HybridApplicative => {
                self._beta_once_call_by_value();
                self._beta_once_applicative(0)
            }
        }
    }

    fn eval_with_info(&mut self, depth: u32) {
        if SHOW_REDUCTIONS { print!("    {} reduces to ", show_precedence(self, 0, depth)) };
        let copy = self.clone();
        *self = copy.eval().unwrap();
        if SHOW_REDUCTIONS { println!("{}", show_precedence(self, 0, depth)) }
    }

    // the return value indicates if reduction was performed
    fn _beta_once_normal(&mut self, depth: u32) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => self.unabs_ref_mut().unwrap()._beta_once_normal(depth + 1),
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    self.eval_with_info(depth);
                    true
                } else {
                    self.lhs_ref_mut().unwrap()._beta_once_normal(depth) ||
                    self.rhs_ref_mut().unwrap()._beta_once_normal(depth)
                }
            }
        }
    }

    // the return value indicates if reduction was performed
    fn _beta_once_call_by_name(&mut self) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => false,
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    self.eval_with_info(0);
                    true
                } else {
                    self.lhs_ref_mut().unwrap()._beta_once_call_by_name() ||
                    self.rhs_ref_mut().unwrap()._beta_once_call_by_name()
                }
            }
        }
    }

    // the return value indicates if reduction was performed
    fn _beta_once_head_spine(&mut self, depth: u32, is_head: bool) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => if is_head {
                self.unabs_ref_mut().unwrap()._beta_once_head_spine(depth + 1, is_head)
            } else {
                false
            },
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    self.eval_with_info(0);
                    true
                } else {
                    self.lhs_ref_mut().unwrap()._beta_once_head_spine(depth, is_head) ||
                    self.rhs_ref_mut().unwrap()._beta_once_head_spine(depth, false)
                }
            }
        }
    }

    // the return value indicates if reduction was performed
    fn _beta_once_applicative(&mut self, depth: u32) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => self.unabs_ref_mut().unwrap()._beta_once_applicative(depth + 1),
            App(_, _) => {
                if !self.lhs_ref().unwrap().is_beta_reducible(&Applicative) &&
                   !self.rhs_ref().unwrap().is_beta_reducible(&Applicative) &&
                    self.lhs_ref().unwrap().unabs_ref().is_ok()
                {
                    self.eval_with_info(depth);
                    true
                } else {
                    self.lhs_ref_mut().unwrap()._beta_once_applicative(depth) ||
                    self.rhs_ref_mut().unwrap()._beta_once_applicative(depth)
                }
            }
        }
    }

    // the return value indicates if reduction was performed
    fn _beta_once_call_by_value(&mut self) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => false,
            App(_, _) => {
                if !self.lhs_ref().unwrap().is_beta_reducible(&CallByValue) &&
                   !self.rhs_ref().unwrap().is_beta_reducible(&CallByValue) &&
                    self.lhs_ref().unwrap().unabs_ref().is_ok()
                {
                    self.eval_with_info(0);
                    true
                } else {
                    self.lhs_ref_mut().unwrap()._beta_once_call_by_value() ||
                    self.rhs_ref_mut().unwrap()._beta_once_call_by_value()
                }
            }
        }
    }

    /// Checks whether `self` is β-reducible under the specified evaluation `Order`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::{succ, zero};
    /// use lambda_calculus::reduction::Order;
    ///
    /// let reducible     = succ().app(1.into());
    /// let not_reducible = zero();
    ///
    /// assert!(reducible.is_beta_reducible(&Order::Normal));
    /// assert!(!not_reducible.is_beta_reducible(&Order::Normal));
    /// ```
    pub fn is_beta_reducible(&self, order: &Order) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => match *order {
                Normal | Applicative => self.unabs_ref().unwrap().is_beta_reducible(order),
                _ => false
            },
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    true
                } else {
                    self.lhs_ref().unwrap().is_beta_reducible(order) ||
                    self.rhs_ref().unwrap().is_beta_reducible(order)
                }
            }
        }
    }

    /// Performs full β-reduction on `self` using the specified evaluation `Order`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    /// use lambda_calculus::reduction::Order;
    ///
    /// let mut pred_one = pred().app(1.into());
    /// pred_one.beta_full(&Order::Normal);
    ///
    /// assert_eq!(pred_one, 0.into());
    /// ```
    pub fn beta_full(&mut self, order: &Order) {
        loop {
            if SHOW_REDUCTIONS { println!("reducing {}", self) }
            if !self.beta_once_indicative(order) { break }
        }
        if SHOW_REDUCTIONS { println!("    doesn't reduce") }
    }
}

/// Performs full β-reduction on a `Term` using the specified evaluation `Order`, consuming its
/// argument in the process.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::pred;
/// use lambda_calculus::reduction::{beta_full, Order};
///
/// let pred_one = pred().app(1.into());
///
/// assert_eq!(beta_full(pred_one, &Order::Normal), 0.into());
/// ```
pub fn beta_full(mut term: Term, order: &Order) -> Term {
    term.beta_full(order);
    term
}

/// Performs a single β-reduction on a `Term` using the specified evaluation `Order`, consuming its
/// argument in the process.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::succ;
/// use lambda_calculus::reduction::{beta_once, Order};
///
/// let succ_one = succ().app(1.into());
///
/// assert_eq!(beta_once(succ_one, &Order::Normal), succ().apply(&1.into()).unwrap());
/// ```
pub fn beta_once(mut term: Term, order: &Order) -> Term {
    term.beta_once(order);
    term
}

#[cfg(test)]
mod test {
    use super::*;
    use parser::parse;
    use combinators::{i, y};

    #[test]
    fn normal_order() {
        let reduces_instantly = parse(&"(λλ1)((λλλ((32)1))(λλ2))").unwrap();
        assert_eq!(beta_full(reduces_instantly.clone(), &Normal),
                   beta_once(reduces_instantly, &Normal));

        let should_reduce = parse(&"(λ2)((λ111)(λ111))").unwrap();
        assert_eq!(beta_full(should_reduce, &Normal), Var(1))
    }

    #[test]
    fn call_by_name_order() {
        let mut expr = app(abs(app(i(), Var(1))), app(i(), i()));
        expr.beta_once(&CallByName);
        assert_eq!(expr, app(i(), app(i(), i())));
        expr.beta_once(&CallByName);
        assert_eq!(expr, app(i(), i()));
        expr.beta_once(&CallByName);
        assert_eq!(expr, i());
    }

    #[test]
    fn applicative_order() {
        let expr = parse(&"λ1(((λλλ1)1)((λλ21)1))").unwrap();
        assert_eq!(&format!("{}", beta_once(expr, &Applicative)), "λ1((λλ1)((λλ21)1))");

        let expands = parse(&"(λ2)((λ111)(λ111))").unwrap();
        assert_eq!(&format!("{}", beta_once(expands, &Applicative)), "(λ2)((λ111)(λ111)(λ111))")
    }

    #[test]
    fn call_by_value_order() {
        let mut expr = app(abs(app(i(), Var(1))), app(i(), i()));
        expr.beta_once(&CallByValue);
        assert_eq!(expr, app(abs(app(i(), Var(1))), i()));
        expr.beta_once(&CallByValue);
        assert_eq!(expr, app(i(), i()));
        expr.beta_once(&CallByValue);
        assert_eq!(expr, i());
    }

    #[test]
    fn reducibility() {
        assert!(y().is_beta_reducible(&Normal));
        assert!(y().is_beta_reducible(&Applicative));
        assert!(!y().is_beta_reducible(&CallByName));
        assert!(!y().is_beta_reducible(&CallByValue));
    }
}
