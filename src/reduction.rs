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

// TODO: untested; check if works, add tests
pub fn beta_reduce_once(term: &mut Term) {
    let mut done = false;

    _beta_reduce_once(term, &mut done)
}

fn _beta_reduce_once(term: &mut Term, done: &mut bool) {
    if *done == true { return }

    match *term {
        Var(_) => (),
        Abs(_) => {
            beta_reduce(term.unabs_ref_mut().unwrap()) // safe
        },
        App(_, _) => {
            beta_reduce(term.lhs_ref_mut().unwrap()); // safe
            beta_reduce(term.rhs_ref_mut().unwrap()); // safe

            let copy = term.clone();
            if let Ok(result) = copy.eval() {
                *term = result;
                *done = true
            }
        }
    }
}

// TODO: sometimes needs to be applied a few times; test more
pub fn beta_reduce(term: &mut Term) {
    match *term {
        Var(_) => (),
        Abs(_) => {
            beta_reduce(term.unabs_ref_mut().unwrap()) // safe
        },
        App(_, _) => {
            beta_reduce(term.lhs_ref_mut().unwrap()); // safe
            beta_reduce(term.rhs_ref_mut().unwrap()); // safe

            let copy = term.clone();
            if let Ok(result) = copy.eval() {
                *term = result;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use arithmetic::{succ, pred};
    use super::beta_reduce;

    #[test]
    fn weak_head_normal_form() {
        // TODO
    }

    #[test]
    fn beta_reduction() {
        let mut succ = succ().apply(0.into()).unwrap();
        let mut pred = pred().apply(1.into()).unwrap();
        beta_reduce(&mut succ);

        println!("{}", pred);
        beta_reduce(&mut pred);
        println!("{}", pred);
        beta_reduce(&mut pred);
        println!("{}", pred);
        beta_reduce(&mut pred);
        println!("{}", pred);

        assert_eq!(succ, 1.into());
        assert_eq!(pred, 0.into());
    }
}
