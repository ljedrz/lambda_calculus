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

// WIP; doesn't fully reduce after multiple applications
/// Performs a single β-reduction on `self`
///
/// # Example
///
/// ```
/// use lambda_calculus::reduction::beta_reduce_once;
/// use lambda_calculus::arithmetic::pred;
///
/// // PRED := λλλ3(λλ1(24))(λ2)(λ1)
/// let mut pred_one = pred().apply(1.into()).unwrap();
/// beta_reduce_once(&mut pred_one);
///
/// assert_eq!(&*format!("{}", pred_one), "λλ(λ(λλ1(35))1)(λ2)(λ1)");
/// ```
pub fn beta_reduce_once(term: &mut Term) {
    println!("reducing {}", term);

    match *term {
        Var(_) => (),
        Abs(_) => {
            beta_reduce_once(term.unabs_ref_mut().unwrap()) // safe
        },
        App(_, _) => {
            let copy = term.clone();
            if let Ok(result) = copy.eval() {
                println!("\treduced {} to {}", term, result);
                *term = result;
                return
            }
            if term.lhs_ref().unwrap().unvar_ref().is_err() {
                beta_reduce_once(term.lhs_ref_mut().unwrap()) // safe
            } else if term.rhs_ref().unwrap().unvar_ref().is_err() {
                beta_reduce_once(term.rhs_ref_mut().unwrap()) // safe
            }
        }
    }
}

// TODO: needs to be applied a few times; test more; check eval order
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
    use super::{beta_reduce_once};
    use term::Term;

    #[test]
    fn weak_head_normal_form() {
        // TODO
    }

    #[test]
    fn succ_beta_reduction() {
        //println!("({})({})", succ(), Term::from(1));
        let mut succ_one = succ().apply(1.into()).unwrap();
        for _ in 0..3 {
            beta_reduce_once(&mut succ_one);
        }
        assert_eq!(&*format!("{}", succ_one), "λλ2(21)")
    }

    #[test]
    fn pred_beta_reduction() {
        //println!("({})({})", pred(), Term::from(1));
        let mut pred_one = pred().apply(1.into()).unwrap();
        for _ in 0..6 {
            beta_reduce_once(&mut pred_one);
        }
        assert_eq!(&*format!("{}", pred_one), "λλ1")
    }
/*
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
*/
}
