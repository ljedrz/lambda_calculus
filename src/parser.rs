#![allow(dead_code)]

use term::*;
use term::Term::*;
use self::Token::*;
use self::Error::*;

#[derive(Debug, PartialEq)]
enum Error {
    InvalidCharacter((usize, char))
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

#[derive(Debug)]
struct Parser {
    output: Vec<Term>,
    stack: Vec<Token>,
    temp: Vec<Term>
}

impl Parser {
    fn new() -> Parser {
        Parser { output: Vec::new(), stack: Vec::new(), temp: Vec::new() }
    }

    fn process(&mut self, tokens: &[Token]) -> Result<Term, Error> {
        let mut iter = tokens.iter();

        while let Some(&token) = iter.next() {
            println!("stack: {:?}; output: {:?}; temp: {:?}", self.stack, self.output, self.temp);
            match token {
                Lambda => {
                    self.stack.push(token)
                },
                Lparen => {
                    while !self.temp.is_empty() {
                        self.output.push(self.temp.pop().unwrap())
                    }
                    self.stack.push(token)
                },
                Rparen => {
                    if !self.temp.is_empty() {

                        let mut ret = fold_terms(self.temp.clone());
                        while self.stack.last() == Some(&Lambda) {
                            ret = abs(ret);
                        }
                        self.output.push(ret);

//                        self.output.push(fold_terms(self.temp.clone())); // TODO: some swap or other smartery
                        self.temp.clear();
                    }
                    self.stack.pop(); // drop Lparen; TODO: check if Lparen
                },
                Index(i) => {
                    if self.stack.contains(&Lparen) {
                        self.temp.push(Var(i))
                    } else {
                        self.output.push(Var(i))
                    }
                }
            }
        }

        let mut ret = fold_terms(self.output.clone());

        while let Some(Lambda) = self.stack.pop() {
            ret = abs(ret);
        }

        println!("{:?}", self);

        Ok(ret)
    }

    fn parse(&mut self, string: &str) -> Result<Term, Error> {
        let mut lexer = Lexer::new();
        try!(lexer.tokenize(string));
        let mut parser = Parser::new();
        parser.process(&lexer.tokens)
    }
}

fn fold_terms(mut terms: Vec<Term>) -> Term {
//    println!("folding terms {:?}", terms);
    if terms.len() > 1 {
        terms.reverse();
        let fst = terms.pop().unwrap();
        terms.reverse();
        terms.into_iter().fold(fst, |acc, t| app(acc, t))
    } else {
        terms.pop().unwrap()
    }
}
/*
pub fn split_parenthesized(input: &str) -> (&str, &str) {
    let mut pos = 1;
    let mut depth = 1;
    let mut chars = input.chars().skip(1);

    while let Some(c) = chars.next() {
        if depth == 0 {
            break;
        } else if c == '(' {
            depth += 1;
        } else if c == ')' {
            depth -= 1;
        }
        if c == 'λ' { pos += 2 } else { pos += 1 }
    }
//    println!("input has a parens \"{}\" and rest \"{}\"", &input[1..pos-1], &input[pos..]);
    (&input[1..pos-1], &input[pos..])
}
*/
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
    fn parse_succ() {
        let succ = "λλλ2(321)";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&succ).unwrap()), "λλλ2(321)");
    }
*/
    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&y).unwrap()), "λ(λ2(11))(λ2(11))");
    }
}
