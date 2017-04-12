#![allow(dead_code)]

use term::*;
use term::Term::*;
use self::Token::*;
use self::Error::*;
use self::Expression::*;

#[derive(Debug, PartialEq)]
enum Error {
    InvalidCharacter((usize, char)),
    InvalidExpression
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Token {
    Lambda,
    Lparen,
    Rparen,
    Index(usize)
}

#[derive(Debug)]
struct Lexer {
    tokens: Vec<Token>,
    position: usize
}

impl Lexer {
    fn new() -> Lexer {
        Lexer { tokens: Vec::new(), position: 0 }
    }

    fn tokenize(&mut self, input: &str) -> Result<(), Error> {
        let mut chars = input.chars();

        while let Some(c) = chars.next() {
            match c {
                'λ' => { self.tokens.push(Lambda) },
                '(' => { self.tokens.push(Lparen) },
                ')' => { self.tokens.push(Rparen) },
                 x  => {
                    if let Some(i) = x.to_digit(16) {
                        self.tokens.push(Index(i as usize))
                    } else if x.is_whitespace() {
                        ()
                    } else {
                        return Err(InvalidCharacter((self.position, x)))
                    }
                }
            }
            self.position += if c == 'λ' { 2 } else { 1 };
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Abstraction,
    Application(Vec<Expression>),
    Variable(usize),
}

fn get_expression(tokens: &[Token], pos: &mut usize) -> Expression {
    let mut expr = Vec::new();

    while *pos < tokens.len() {
        match tokens[*pos] {
            Lambda => {
                expr.push(Abstraction)
            },
            Lparen => {
                *pos += 1;
                let subexpr = get_expression(&tokens, pos);
                expr.push(subexpr);
            },
            Rparen => {
                return Application(expr)
            },
            Index(i) => {
                expr.push(Variable(i))
            }
        }
        *pos += 1;
    }

    Application(expr)
}

fn parse(input: &str) -> Result<Term, Error> {
    let mut lexer = Lexer::new();
    try!(lexer.tokenize(input));

    let mut pos = 0;
    let ast = get_expression(&lexer.tokens, &mut pos);

    let exprs = if let Application(exprs) = ast { Ok(exprs) } else { Err(InvalidExpression) };

    let mut stack = Vec::new();
    let mut output = Vec::new();
    let term = fold_exprs(&exprs.unwrap(), &mut stack, &mut output);

    println!("{}", term);

    Ok(term)
}

fn fold_exprs(exprs: &[Expression], stack: &mut Vec<Expression>, output: &mut Vec<Term>) -> Term {
    println!("exprs: {:?}; s: {:?}; o: {:?}", exprs, stack, output);

    let mut iter = exprs.iter();

    while let Some(ref expr) = iter.next() {
        match **expr {
            Abstraction            => stack.push(Abstraction),
            Application(ref exprs) => {
                let mut out2 = Vec::new();
                let mut sta2 = Vec::new();
                output.push(fold_exprs(&exprs, &mut sta2, &mut out2))
            },
            Variable(i)            => output.push(Var(i))
        }
    }

    let mut ret = fold_terms(output.clone());

    while let Some(Abstraction) = stack.pop() {
        ret = abs(ret);
    }

    ret
}

/*
fn fold_exprs(exprs: &[Expression]) -> Term {
    println!("folding {:?}", exprs);
    match exprs[0] {
        Variable(i) => {
            if exprs[1..].is_empty() {
                Var(i)
            } else {
                fold_terms(vec![Var(i), fold_exprs(&exprs[1..])])
            }
        },
        Abstraction => abs(fold_exprs(&exprs[1..])),
        Application(ref exprs2) => {
            if exprs[1..].is_empty() {
                fold_exprs(&exprs2)
            } else {
                fold_terms(vec![fold_exprs(&exprs2), fold_exprs(&exprs[1..])])
            }
        }
    }
}
*/
fn fold_terms(mut terms: Vec<Term>) -> Term {
//    println!("folding terms {:?}", terms);
    if terms.len() > 1 {
        terms.reverse();
        let fst = terms.pop().expect("popped an empty term list");
        terms.reverse();
        terms.into_iter().fold(fst, |acc, t| app(acc, t))
    } else {
        terms.pop().unwrap()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn tokenization_error() {
        let fail = "λλx2";
        let mut lexer = Lexer::new();

        assert_eq!(lexer.tokenize(&fail), Err(InvalidCharacter((4, 'x'))))
    }

    #[test]
    fn tokenization_success() {
        let quine = "λ 1 ( (λ 1 1) (λ λ λ λ λ 1 4 (3 (5 5) 2) ) ) 1";
        let mut lexer = Lexer::new();

        assert!(lexer.tokenize(&quine).is_ok());
        assert_eq!(lexer.tokens, vec![Lambda, Index(1), Lparen, Lparen, Lambda, Index(1), Index(1), Rparen, Lparen, Lambda,
                                      Lambda, Lambda, Lambda, Lambda, Index(1), Index(4), Lparen, Index(3), Lparen, Index(5),
                                      Index(5), Rparen, Index(2), Rparen, Rparen, Rparen, Index(1)]
        )
    }
/*
    #[test]
    fn succ_ast() {
        let succ = "λλλ2(321)";
        let mut lexer = Lexer::new();

        assert!(lexer.tokenize(&succ).is_ok());

    }
*/
    #[test]
    fn parse_succ() {
        let succ = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))(λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";

        assert_eq!(&*format!("{}", parse(&succ).unwrap()), succ);
    }

/*
    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        let mut parser = Parser::new(&y);

        println!("{:?}", parser.ast);

        assert_eq!(&*format!("{}", parser.parse(&y).unwrap()), y);
    }
*/
/*
    #[test]
    fn parse_quine() {
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&quine).unwrap()), quine);
    }

    #[test]
    fn parse_blc() {
        let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))(λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&blc).unwrap()), blc);
    }
    */
}
