//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

use term::*;
use term::Term::*;
use self::Order::*;

/// Set to `true` to see all the steps of β-reductions. The default is `false`.
pub const SHOW_REDUCTIONS: bool = false;

/// The [evaluation order](https://en.wikipedia.org/wiki/Lambda_calculus#Reduction_strategies) of 
/// β-reductions. `Applicative` order will not fully reduce expressions containing functions 
/// without a normal form, e.g. the Y combinator. The default is `Normal`.
pub const EVALUATION_ORDER: Order = Normal;

/// The available variants of β-reduction evaluation order.
#[derive(Debug, PartialEq)]
pub enum Order {
    Normal,
    Applicative
}

/// Applies two terms with substitution and variable update, consuming the first one in the process.
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
    /// Applies `self` to another term with substitution and variable update, consuming it
    /// in the process.
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

    /// Performs a single β-reduction on `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::succ;
    ///
    /// let mut succ_one = succ().app(1.into());
    /// succ_one.beta_once();
    ///
    /// assert_eq!(succ_one, succ().apply(&1.into()).unwrap());
    /// ```
    pub fn beta_once(&mut self) {
        match EVALUATION_ORDER {
            Normal => self._beta_once_normal(0),
            Applicative => self._beta_once_applicative(0)
        };
    }

    // the return value indicates if reduction was performed
    fn _beta_once_normal(&mut self, depth: u32) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => self.unabs_ref_mut().unwrap()._beta_once_normal(depth + 1),
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    let copy = self.clone();
                    if SHOW_REDUCTIONS { print!("    {} reduces to ", show_precedence(self, 0, depth)) };
                    *self = copy.eval().unwrap();
                    if SHOW_REDUCTIONS { println!("{}", show_precedence(self, 0, depth)) }
                    true
                } else {
                    if !self.lhs_ref_mut().unwrap()._beta_once_normal(depth) {
                        self.rhs_ref_mut().unwrap()._beta_once_normal(depth)
                    } else {
                        true
                    }
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
                if !self.lhs_ref().unwrap().is_beta_reducible() &&
                   !self.rhs_ref().unwrap().is_beta_reducible() &&
                    self.lhs_ref().unwrap().unabs_ref().is_ok()
                {
                    let copy = self.clone();
                    if SHOW_REDUCTIONS { print!("    {} reduces to ", show_precedence(self, 0, depth)) };
                    *self = copy.eval().unwrap();
                    if SHOW_REDUCTIONS { println!("{}", show_precedence(self, 0, depth)) }
                    true
                } else {
                    if !self.lhs_ref_mut().unwrap()._beta_once_applicative(depth) {
                        self.rhs_ref_mut().unwrap()._beta_once_applicative(depth)
                    } else {
                        true
                    }
                }
            }
        }
    }
    
    /// Checks whether `self` is β-reducible.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::{succ, zero};
    ///
    /// let reducible     = succ().app(1.into());
    /// let not_reducible = zero();
    ///
    /// assert!(reducible.is_beta_reducible());
    /// assert!(!not_reducible.is_beta_reducible());
    /// ```
    pub fn is_beta_reducible(&self) -> bool {
        match *self {
            Var(_) => false,
            Abs(_) => self.unabs_ref().unwrap().is_beta_reducible(),
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    true
                } else {
                    self.lhs_ref().unwrap().is_beta_reducible() ||
                    self.rhs_ref().unwrap().is_beta_reducible()
                }
            }
        }
    }

    /// Performs full β-reduction on `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    ///
    /// let mut pred_one = pred().app(1.into());
    /// pred_one.beta_full();
    ///
    /// assert_eq!(pred_one, 0.into());
    /// ```
    pub fn beta_full(&mut self) {
        let mut tmp;
        loop {
            if SHOW_REDUCTIONS { println!("reducing {}", self) }
            tmp = self.clone();
            self.beta_once();
            if *self == tmp { break }
        }

        if SHOW_REDUCTIONS { println!("    doesn't reduce") }
    }
}

/// Performs full β-reduction on a `Term`, consuming it in the process.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::pred;
/// use lambda_calculus::reduction::beta_full;
///
/// let pred_one = pred().app(1.into());
///
/// assert_eq!(beta_full(pred_one), 0.into());
/// ```
pub fn beta_full(mut term: Term) -> Term {
    term.beta_full();
    term
}

/// Performs a single β-reduction on `self`.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::succ;
/// use lambda_calculus::reduction::beta_once;
///
/// let succ_one = succ().app(1.into());
///
/// assert_eq!(beta_once(succ_one), succ().apply(&1.into()).unwrap());
/// ```
pub fn beta_once(mut term: Term) -> Term {
    term.beta_once();
    term
}

#[cfg(test)]
mod test {
    use super::*;
    use parser::parse;
    
    #[test]
    fn evaluation_order() {
        match EVALUATION_ORDER {
            Normal => {
                let should_reduce = parse(&"(λ2)((λ111)(λ111))").unwrap();
                assert_eq!(beta_full(should_reduce), Var(1))
            },
            Applicative => {
                let shouldnt_reduce = parse(&"(λ2)((λ111)(λ111))").unwrap();
                assert_eq!(beta_once(shouldnt_reduce), parse(&"(λ2)((λ111)(λ111)(λ111))").unwrap())
            }
        }
    }
}
