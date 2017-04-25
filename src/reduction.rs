//! [β-reduction](https://en.wikipedia.org/wiki/Beta_normal_form) for lambda `Term`s

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
pub fn normalize(term: Term) -> Term {
    nf(0, term, VecDeque::new())
}

/// Set to `true` to see all the steps of β-reductions. The default is `false`.
pub const SHOW_REDUCTIONS: bool = false;

impl Term {
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
