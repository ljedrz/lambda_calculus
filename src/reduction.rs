//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

#![allow(dead_code)]

use term::*;
use term::Term::*;
use self::Closure::*;
use self::Expression::*;
use std::collections::VecDeque;

#[derive(Debug, PartialEq, Clone)]
enum Closure {
    Depth(usize),
    TermInEnv(Term, Environment)
}

#[derive(Debug, PartialEq)]
enum Expression {
    Evaluation(Closure),
    Application(Box<Expression>, Term, Environment)
}

type Environment = VecDeque<Closure>;

fn whnf(term: Term, mut env: Environment) -> Expression {
    match term {
        Var(i) => match env.remove(i - 1) {
            Some(Depth(i)) => Evaluation(Depth(i)),
            Some(TermInEnv(t, e)) => whnf(t, e),
            None => unreachable!()
        },
        Abs(t) => Evaluation(TermInEnv(Abs(t), env)),
        App(lhs, rhs) => match whnf(*lhs, env.clone()) { // TODO: try to remove this clone()
            Evaluation(TermInEnv(Abs(lhs2), mut env2)) => {
                env2.push_front(TermInEnv(*rhs, env));
                whnf(*lhs2, env2)
            },
            expr => Application(Box::new(expr), *rhs, env)
        }
    }
}

fn reduce(depth: usize, exp: Expression) -> Term {
    match exp {
        Application(lhs, rhs, env) => app(reduce(depth, *lhs), nf(depth, rhs, env)),
        Evaluation(TermInEnv(Abs(term), mut env)) => {
            env.push_front(Depth(depth));
            abs(nf(depth + 1, *term, env))
        },
        Evaluation(TermInEnv(term, _)) => term,
        Evaluation(Depth(i)) => Var(depth - i)
    }
}

fn nf(depth: usize, term: Term, env: Environment) -> Term {
    reduce(depth, whnf(term, env))
}

/// Returns a term reduced to its normal form. Consumes its argument.
///
/// # Example
///
/// ```
/// use lambda_calculus::booleans::{if_else, tru};
/// use lambda_calculus::arithmetic::{zero, one, succ};
/// use lambda_calculus::reduction::normalize;
///
/// assert_eq!(normalize(succ().app(zero())), one());
/// assert_eq!(normalize(if_else().app(tru()).app(one()).app(zero())), one());
/// ```
fn normalize(term: Term) -> Term {
    nf(0, term, VecDeque::new())
}

/// Applies two terms with substitution and variable update, consuming them in the process.
///
/// # Example
/// ```
/// use lambda_calculus::term::apply;
/// use lambda_calculus::parser::parse;
///
/// let lhs    = parse(&"λλ42(λ13)").unwrap();
/// let rhs    = parse(&"λ51").unwrap();
/// let result = parse(&"λ3(λ61)(λ1(λ71))").unwrap();
///
/// assert_eq!(apply(lhs, rhs), Ok(result));
/// ```
pub fn apply(mut lhs: Term, rhs: Term) -> Result<Term, Error> {
    _apply(&mut lhs, rhs, 0);

    lhs.unabs()
}

fn _apply(lhs: &mut Term, rhs: Term, depth: usize) {
    match *lhs {
        Var(i) => if i == depth {
            *lhs = rhs; // substitute a top-level variable from lhs with rhs
            update_free_variables(lhs, depth - 1, 0); // update indices of free variables from rhs
        } else if i > depth {
            *lhs = Var(i - 1) // decrement a free variable's index
        },
        Abs(_) => {
            _apply(lhs.unabs_ref_mut().unwrap(), rhs, depth + 1)
        },
        App(_, _) => {
            _apply(lhs.lhs_ref_mut().unwrap(), rhs.clone(), depth);
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

/// Set to `true` to see all the steps of β-reductions. The default is `false`.
pub const SHOW_REDUCTIONS: bool = false;

impl Term {
    /// Applies `self` to another term with substitution and variable update, consuming them
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
    /// assert_eq!(lhs.apply(rhs), Ok(result));
    /// ```
    pub fn apply(self, rhs: Term) -> Result<Term, Error> {
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
    /// assert_eq!(app(i(), zero()).eval(), Ok(abs(abs(Var(1)))));
    /// ```
    pub fn eval(self) -> Result<Term, Error> {
        let (lhs, rhs) = try!(self.unapp());

        apply(lhs, rhs)
    }

    /// Performs a single normal-order β-reduction on `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::succ;
    ///
    /// // SUCC := λ λ λ 2 (3 2 1), ONE := λ λ 2 1
    /// let mut succ_one = succ().app(1.into());
    /// succ_one.beta_once();
    ///
    /// assert_eq!(&*format!("{}", succ_one), "λλ2((λλ21)21)");
    /// ```
    pub fn beta_once(&mut self) {
        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_once(),
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    let copy = self.clone();
                    let reduced = copy.eval().unwrap();
                    if SHOW_REDUCTIONS { println!("    {} reduces to {}", self, reduced) };
                    *self = reduced;
                } else {
                    self.lhs_ref_mut().unwrap().beta_once();
                    self.rhs_ref_mut().unwrap().beta_once()
                }
            }
        }
    }

    /// Performs full normal-order β-reduction on `self`.
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
        loop {
            if SHOW_REDUCTIONS { println!("reducing {}", self) }
            let tmp = self.clone();
            self.beta_once();
            if *self == tmp { break }
        }

        if SHOW_REDUCTIONS { println!("    doesn't reduce") }
    }
}

/// Performs full normal-order β-reduction on a `Term`, consuming it in the process.
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

/// Performs a single normal-order β-reduction on `self`.
///
/// # Example
///
/// ```
/// use lambda_calculus::arithmetic::succ;
/// use lambda_calculus::reduction::beta_once;
///
/// // SUCC := λ λ λ 2 (3 2 1), ONE := λ λ 2 1
/// let succ_one = succ().app(1.into());
///
/// assert_eq!(&*format!("{}", beta_once(succ_one)), "λλ2((λλ21)21)");
/// ```
pub fn beta_once(mut term: Term) -> Term {
    term.beta_once();
    term
}

#[cfg(test)]
mod test {

    #[test]
    fn weak_head_normal_form() {
        // TODO
    }
}
