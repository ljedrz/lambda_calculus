use term::Term;
use term::Term::*;
use std::fmt;
use std::borrow::Cow;

fn parenthesize_if(condition: bool, input: &str) -> Cow<str> {
	if condition {
		format!("({})", input).into()
	} else {
		input.into()
	}
}

fn show_precedence(context_precedence: usize, term: &Term) -> String {
	match *term {
		Var(i) => format!("{:X}", i), // max. index = 15
		Abs(ref t) => {
			let ret = format!("λ{}", t);
			parenthesize_if(context_precedence > 1, &ret).into()
		},
		App(ref t1, ref t2) => {
			let ret = format!("{}{}", show_precedence(2, t1), show_precedence(3, t2));
			parenthesize_if(context_precedence == 3, &ret).into()
		}
	}
}

impl fmt::Display for Term {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", show_precedence(0, self))
	}
}

#[cfg(test)]
mod test {
	use arithmetic::*;

	#[test]
	fn displaying_terms() {
		assert_eq!(&format!("{}", zero()), "λλ1");
		assert_eq!(&format!("{}", succ()), "λλλ2(321)");
		assert_eq!(&format!("{}", pred()), "λλλ3(λλ1(24))(λ2)(λ1)");
	}
}