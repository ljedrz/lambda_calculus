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

fn whnf(term: Term, env: Environment) -> Expression {
	match term {
		Var(i) => match env[i - 1].clone() {
			Depth(i) => Evaluation(Depth(i)),
			TermInEnv(t, e) => whnf(t, e)
		},
		Abs(t) => Evaluation(TermInEnv(Abs(t), env)),
		App(lhs, rhs) => match whnf(*lhs, env.clone()) {
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

pub fn normalize(term: Term) -> Term {
	nf(0, term, VecDeque::new())
}

#[cfg(test)]
mod test {
	use arithmetic::*;
	use super::normalize;

	#[test]
	fn weak_head_normal_form() {
		// TODO
	}

	#[test]
	fn normal_form() {
		// TODO: more tests, esp. generic ones
		assert_eq!(normalize(succ().app(zero())), one());
	}
}