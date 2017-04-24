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

impl Term {
    /// Performs a single normal-order β-reduction on `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::succ;
    ///
    /// // SUCC := λ λ λ 2 (3 2 1)
    /// let mut succ_one = succ().apply(1.into()).unwrap();
    /// succ_one.beta_once();
    ///
    /// assert_eq!(&*format!("{}", succ_one), "λλ2((λ31)1)");
    /// ```
    pub fn beta_once(&mut self) {
        match *self {
            Var(_) => (),
            Abs(_) => self.unabs_ref_mut().unwrap().beta_once(), // safe
            App(_, _) => {
                let copy = self.clone();
                if let Ok(result) = copy.eval() {
                    // println!("{} reduces to {}", self, result);
                    *self = result
                } else if self.lhs_ref().unwrap().unvar_ref().is_err() {
                    self.lhs_ref_mut().unwrap().beta_once() // safe
                } else {
                    self.rhs_ref_mut().unwrap().beta_once() // safe
                }
            }
        }
    }

    // FIXME: doesn't reduce one last abstraction in PRED ONE
    /// Performs full normal-order β-reduction on `self`.
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    ///
    /// // PRED := λλλ3(λλ1(24))(λ2)(λ1)
    /// let mut pred_one = pred().apply(1.into()).unwrap();
    /// pred_one.beta_full();
    ///
    /// assert_eq!(&*format!("{}", pred_one), "λλ1");
    /// ```
    pub fn beta_full(&mut self) {
        let mut tmp = self.clone();
        self.beta_once();

        while tmp != *self {
            tmp = self.clone();
            self.beta_once();
        }
    }
}

#[cfg(test)]
mod test {
    use arithmetic::{succ, pred, is_zero, one};
    use term::*;
    use term::Term::*;
    use parser::parse;

    #[test]
    fn weak_head_normal_form() {
        // TODO
    }
/*
    #[test]
    fn beta_reduce_tmp() {
        let term = parse(&*"").unwrap();

        term.beta_full();

        assert_eq!(format!("{}", ret), "(λλ1(35))(λ2)")
    }
*/
    #[test]
    fn succ_beta_reduction() {
        //println!("({})({})", succ(), Term::from(1));
        let mut succ_one = succ().apply(1.into()).unwrap();
        succ_one.beta_full();

        assert_eq!(&*format!("{}", succ_one), "λλ2(21)")
    }
/*
    #[test]
    fn pred_beta_reduction() {
        //println!("({})({})", pred(), Term::from(1));
        let mut pred_one = pred().apply(1.into()).unwrap();
        pred_one.beta_full();

        assert_eq!(&*format!("{}", pred_one), "λλ1")
    }
*/
}
