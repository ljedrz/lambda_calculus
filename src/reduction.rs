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
    // WIP; doesn't reduce one last abstraction
    /// Performs a single β-reduction on `self`
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    ///
    /// // PRED := λλλ3(λλ1(24))(λ2)(λ1)
    /// let mut pred_one = pred().apply(1.into()).unwrap();
    /// pred_one.beta_reduce();
    ///
    /// assert_eq!(&*format!("{}", pred_one), "λλ(λ(λλ1(35))1)(λ2)(λ1)");
    /// ```
    pub fn beta_reduce(&mut self) {
        println!("reducing {}", self);
        let mut is_under_abs = false;
        self._beta_reduce(&mut is_under_abs);

        if is_under_abs {
            let copy = self.clone();
            *self = copy.unabs().unwrap();
        }
        println!("the result is {}\n", self);
    }

    // indicates whether the reduced term was under an abstraction
    fn _beta_reduce(&mut self, is_under_abs: &mut bool) {

        match *self {
            Var(_) => {
                *is_under_abs = false;
            },
            Abs(_) => {
                *is_under_abs = true;
                self.unabs_ref_mut().unwrap()._beta_reduce(is_under_abs); // safe
            },
            App(_, _) => {
                if self.lhs_ref().unwrap().unabs_ref().is_ok() {
                    *is_under_abs = false;
                }

                let copy = self.clone();
                if let Ok(result) = copy.eval() {
                    println!("{} reduces to {}", self, result);
                    *self = result;
                    return
                }

                *is_under_abs = false;

                if self.lhs_ref().unwrap().unvar_ref().is_err() {
                    self.lhs_ref_mut().unwrap()._beta_reduce(is_under_abs) // safe
                } else if self.rhs_ref().unwrap().unvar_ref().is_err() {
                    self.rhs_ref_mut().unwrap()._beta_reduce(is_under_abs) // safe
                }
            }
        }
    }

    /// Performs full β-reduction on `self`
    ///
    /// # Example
    ///
    /// ```
    /// use lambda_calculus::arithmetic::pred;
    ///
    /// // PRED := λλλ3(λλ1(24))(λ2)(λ1)
    /// let mut pred_one = pred().apply(1.into()).unwrap();
    /// pred_one.beta_reduce_full();
    ///
    /// assert_eq!(&*format!("{}", pred_one), "λλ1");
    /// ```
    pub fn beta_reduce_full(&mut self) {
        let mut tmp = self.clone();
        self.beta_reduce();

        while tmp != *self {
            tmp = self.clone();
            self.beta_reduce();
        }
    }
}

#[cfg(test)]
mod test {
    use arithmetic::{succ, pred, is_zero, one};
    use term::*;
    use term::Term::*;

    #[test]
    fn weak_head_normal_form() {
        // TODO
    }

    #[test]
    fn succ_beta_reduction() {
        //println!("({})({})", succ(), Term::from(1));
        let mut succ_one = succ().apply(1.into()).unwrap();
        succ_one.beta_reduce_full();

        assert_eq!(&*format!("{}", succ_one), "λλ2(21)")
    }
/*
    #[test]
    fn pred_beta_reduction() {
        //println!("({})({})", pred(), Term::from(1));
        let mut pred_one = pred().apply(1.into()).unwrap();
        pred_one.beta_reduce_full();

        assert_eq!(&*format!("{}", pred_one), "λλ1")
    }
*/
}
