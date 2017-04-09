use term::*;
use term::Term::*;

fn _parse(input: &str, depth: usize) -> Option<(Term, &str)> {
    let c = input.chars().next();

    match c {
        Some('λ') => {
            if let Some((term, rest)) = _parse(&input[2..], depth) {
                Some((abs(term), rest))
            } else {
                None
            }
        },
        Some('(') => {
            let range = input[1..].chars().take_while(|&c| c != ')');
            Some((app(parse(&input[1..range]), parse(&input[range..])), &input))
        },
        Some(')') => _parse(&input[1..], depth),
        Some(x) => Some((Var(x.to_digit(16).unwrap() as usize), &input[1..])),
        _ => None
    }
}

pub fn parse(input: &str) -> Term {
    _parse(input, 0).unwrap().0
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parsing() {
        let tru = "λλ2";
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";

        assert_eq!(parse(tru), abs(abs(Var(2))));
        assert_eq!(format!("{}", parse(quine)), quine);
    }
}
