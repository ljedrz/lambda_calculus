//! A parser for lambda expressions with [De Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index)

use term::*;
use term::Term::*;
use self::Token::*;
use self::Error::*;
use self::Expression::*;

/// A type to represent a parsing error.
#[derive(Debug, PartialEq)]
pub enum Error {
    InvalidCharacter((usize, char)),
    InvalidExpression
}

#[derive(Debug, PartialEq)]
enum Token {
    Lambda,
    Lparen,
    Rparen,
    Number(usize)
}

fn tokenize(input: &str) -> Result<Vec<Token>, Error> {
    let mut chars = input.chars();
    let mut tokens = Vec::new();
    let mut position = 0;

    while let Some(c) = chars.next() {
        match c {
            'λ' => { tokens.push(Lambda) },
            '(' => { tokens.push(Lparen) },
            ')' => { tokens.push(Rparen) },
             x  => {
                if let Some(n) = x.to_digit(16) {
                    tokens.push(Number(n as usize))
                } else if x.is_whitespace() {
                    ()
                } else {
                    return Err(InvalidCharacter((position, x)))
                }
            }
        }
        position += if c == 'λ' { 2 } else { 1 };
    }

    Ok(tokens)
}

#[derive(Debug, PartialEq)]
enum Expression {
    Abstraction,
    Sequence(Vec<Expression>),
    Variable(usize)
}

fn _get_ast(tokens: &[Token], pos: &mut usize) -> Expression {
    let mut expr = Vec::new();

    while *pos < tokens.len() {
        match tokens[*pos] {
            Lambda => {
                expr.push(Abstraction)
            },
            Number(i) => {
                expr.push(Variable(i))
            },
            Lparen => {
                *pos += 1;
                expr.push(_get_ast(&tokens, pos));
            },
            Rparen => {
                return Sequence(expr)
            }
        }
        *pos += 1;
    }

    Sequence(expr)
}

fn get_ast(tokens: &[Token]) -> Expression {
    let mut pos = 0;

    _get_ast(tokens, &mut pos)
}

/// Parses the input lambda expression to a `Term`.
///
/// # Example
/// ```
/// use lambda_calculus::parser::parse;
/// use lambda_calculus::arithmetic::{succ, pred};
///
/// assert_eq!(parse(&"λ λ λ 2 (3 2 1)"), Ok(succ()));
/// assert_eq!(parse(&"λλλ3(λλ1(24))(λ2)(λ1)"), Ok(pred()));
/// ```
pub fn parse(input: &str) -> Result<Term, Error> {
    let tokens = try!(tokenize(input));
    let ast = get_ast(&tokens);

    let exprs = if let Sequence(exprs) = ast { Ok(exprs) } else { Err(InvalidExpression) };

    let mut stack = Vec::new();
    let mut output = Vec::new();
    let term = fold_exprs(&exprs.unwrap(), &mut stack, &mut output);

    Ok(term)
}

fn fold_exprs(exprs: &[Expression], stack: &mut Vec<Expression>, output: &mut Vec<Term>) -> Term {
    let mut iter = exprs.iter();

    while let Some(ref expr) = iter.next() {
        match **expr {
            Variable(i) => output.push(Var(i)),
            Abstraction => stack.push(Abstraction),
            Sequence(ref exprs) => {
                let mut stack2 = Vec::new();
                let mut output2 = Vec::new();
                output.push(fold_exprs(&exprs, &mut stack2, &mut output2))
            }
        }
    }

    let mut ret = fold_terms(output.drain(..).collect());

    while let Some(Abstraction) = stack.pop() {
        ret = abs(ret);
    }

    ret
}

fn fold_terms(mut terms: Vec<Term>) -> Term {
    if terms.len() > 1 {
        terms.reverse();
        let fst = terms.pop().unwrap();
        terms.reverse();
        terms.into_iter().fold(fst, |acc, t| app(acc, t))
    } else {
        terms.pop().expect("attempted to fold an empty term vector")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn tokenization_error() {
        assert_eq!(tokenize(&"λλx2"), Err(InvalidCharacter((4, 'x'))))
    }

    #[test]
    fn tokenization_success() {
        let quine = "λ 1 ( (λ 1 1) (λ λ λ λ λ 1 4 (3 (5 5) 2) ) ) 1";
        let tokens = tokenize(&quine);

        assert!(tokens.is_ok());
        assert_eq!(tokens.unwrap(), vec![Lambda, Number(1), Lparen, Lparen, Lambda, Number(1), Number(1), Rparen, Lparen, Lambda, Lambda, Lambda, Lambda,
            Lambda, Number(1), Number(4), Lparen, Number(3), Lparen, Number(5), Number(5), Rparen, Number(2), Rparen, Rparen, Rparen, Number(1)]);
    }

    #[test]
    fn succ_ast() {
        let tokens = tokenize(&"λλλ2(321)").unwrap();
        let ast = get_ast(&tokens);

        assert_eq!(ast,
            Sequence(vec![
                Abstraction,
                Abstraction,
                Abstraction,
                Variable(2),
                Sequence(vec![
                    Variable(3),
                    Variable(2),
                    Variable(1)
                ])
            ])
        );
    }

    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        assert_eq!(&*format!("{}", parse(&y).unwrap()), y);
    }

    #[test]
    fn parse_quine() {
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";
        assert_eq!(&*format!("{}", parse(&quine).unwrap()), quine);
    }

    #[test]
    fn parse_blc() {
        let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))(λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        assert_eq!(&*format!("{}", parse(&blc).unwrap()), blc);
    }
}
