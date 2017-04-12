#![allow(dead_code)]

use term::*;
use term::Term::*;
use self::Token::*;
use self::Error::*;

#[derive(Debug, PartialEq)]
enum Error {
    InvalidCharacter((usize, char)),
    UnmatchedParentheses
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
                        let ret = if !self.output.is_empty() {
                            fold_terms(vec![self.output.pop().unwrap(), fold_terms(self.temp.clone())])
                        } else {
                            fold_terms(self.temp.clone())
                        };
                        self.output.push(ret); // TODO: some swap or other smartery
                        self.temp.clear();
                    }

                    if self.stack.last() == Some(&Lambda) {
                        let mut ret = self.output.pop().unwrap();
                        while self.stack.last() == Some(&Lambda) {
                            ret = abs(ret);
                            self.stack.pop();
                        }
                        self.output.push(ret);
                    }

                    if self.stack.last() == Some(&Lparen) {
                        self.stack.pop(); // drop matching Lparen
                    } else {
                        return Err(UnmatchedParentheses)
                    }
                },
                Index(i) => {
                    if self.stack.contains(&Lparen) {
                        self.temp.push(Var(i))
                    } else {
                        self.output.push(Var(i))
                    }
                }
            }
            println!("s: {:?}; o: {:?}; t: {:?}", self.stack, self.output, self.temp);
        }

        let mut ret = fold_terms(self.output.clone());

        while let Some(Lambda) = self.stack.pop() {
            ret = abs(ret);
        }

//        println!("{:?}", self);

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

    #[test]
    fn parse_succ() {
        let succ = "λλλ2(321)";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&succ).unwrap()), succ);
    }

    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&y).unwrap()), y);
    }

    #[test]
    fn parse_quine() {
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&quine).unwrap()), quine);
    }
/*
    #[test]
    fn parse_blc() {
        let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))(λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        let mut parser = Parser::new();

        assert_eq!(&*format!("{}", parser.parse(&blc).unwrap()), blc);
    }
    */
}
