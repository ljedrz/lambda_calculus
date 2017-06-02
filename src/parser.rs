//! A parser for lambda expressions

use term::*;
use self::Token::*;
use self::CToken::*;
use self::Error::*;
use self::Expression::*;
pub use term::Notation::*;

/// A type to represent a parsing error.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// an invalid character was encountered
    InvalidCharacter((usize, char)),
    /// the expression is invalid
    InvalidExpression,
    /// the expression is empty
    EmptyExpression
}

#[derive(Debug, PartialEq)]
enum Token {
    /// λ or \
    Lambda,
    /// left parenthesis
    Lparen,
    /// right parenthesis
    Rparen,
    /// a number
    Number(usize)
}

#[derive(Debug, PartialEq)]
enum CToken {
    /// an abstraction with a bound variable
    CLambda(String),
    /// left parenthesis
    CLparen,
    /// right parenthesis
    CRparen,
    /// a variable with an identifier
    CName(String)
}

fn tokenize_dbr(input: &str) -> Result<Vec<Token>, Error> {
    let chars = input.chars().enumerate();
    let mut tokens = Vec::new();

    for (i, c) in chars {
        match c {
     '\\' | 'λ' => { tokens.push(Lambda) },
            '(' => { tokens.push(Lparen) },
            ')' => { tokens.push(Rparen) },
             _  => {
                if let Some(n) = c.to_digit(16) {
                    tokens.push(Number(n as usize))
                } else if c.is_whitespace() {
                    ()
                } else {
                    return Err(InvalidCharacter((i + 1, c)))
                }
            }
        }
    }

    Ok(tokens)
}

fn tokenize_cla(input: &str) -> Result<Vec<CToken>, Error> {
    let mut chars = input.chars().enumerate().peekable();
    let mut tokens = Vec::new();
    let valid_chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";

    while let Some((i, c)) = chars.next() {
        match c {
            '\\' | 'λ' => {
                let mut name = String::new();
                while let Some((i, c)) = chars.next() {
                    if c == '.' {
                        break
                    } else if valid_chars.contains(c) {
                        name.push(c)
                    } else {
                        return Err(InvalidCharacter((i + 1, c)))
                    }
                }
                tokens.push(CLambda(name))
            },
            '(' => { tokens.push(CLparen) },
            ')' => { tokens.push(CRparen) },
             _  => {
                if c.is_whitespace() {
                    ()
                } else if valid_chars.contains(c) {
                    let mut name = c.to_string();
                    while let Some(&(_, c)) = chars.peek() {
                        if c.is_whitespace() || c == '(' || c == ')' {
                            break
                        } else {
                            name.push(c);
                            chars.next();
                        }
                    }
                    tokens.push(CName(name))
                } else {
                    return Err(InvalidCharacter((i + 1, c)))
                }
            }
        }
    }

    Ok(tokens)
}

fn convert_classic_tokens(tokens: &[CToken]) -> Vec<Token> {
    _convert_classic_tokens(tokens, &mut Vec::new(), &mut 0)
}

fn _convert_classic_tokens(tokens: &[CToken], stack: &mut Vec<String>, pos: &mut usize) -> Vec<Token>
{
    let mut output = Vec::with_capacity(tokens[*pos..].len());
    let mut inner_stack_count = 0;

    while let Some(token) = tokens.get(*pos) {
        match *token {
            CLambda(ref name) => {
                output.push(Lambda);
                stack.push(name.clone());
                inner_stack_count += 1;
            },
            CLparen => {
                output.push(Lparen);
                *pos += 1;
                output.append(&mut _convert_classic_tokens(tokens, stack, pos));
            },
            CRparen => {
                output.push(Rparen);
                for _ in 0..inner_stack_count { stack.pop(); }
                return output
            },
            CName(ref name) => {
                if let Some(index) = stack.iter().rev().position(|t| t == name) {
                    output.push(Number(index + 1))
                } else {
                    output.push(Number(stack.len() + 1))
                }
            }
        }
        *pos += 1;
    }

    output
}

#[derive(Debug, PartialEq)]
enum Expression {
    /// an abstraction
    Abstraction,
    /// a sequence of Expressions
    Sequence(Vec<Expression>),
    /// a variable with a De Bruijn index
    Variable(usize)
}

fn get_ast(tokens: &[Token]) -> Result<Expression, Error> {
    _get_ast(tokens, &mut 0)
}

fn _get_ast(tokens: &[Token], pos: &mut usize) -> Result<Expression, Error> {
    if tokens.is_empty() { return Err(EmptyExpression) }

    let mut expr = Vec::new();

    while let Some(token) = tokens.get(*pos) {
        match *token {
            Lambda => {
                expr.push(Abstraction)
            },
            Number(i) => {
                expr.push(Variable(i))
            },
            Lparen => {
                *pos += 1;
                let subtree = try!(_get_ast(tokens, pos));
                expr.push(subtree);
            },
            Rparen => {
                return Ok(Sequence(expr))
            }
        }
        *pos += 1;
    }

    Ok(Sequence(expr))
}

/// Parses the input `&str` as a lambda `Term`.
///
/// - lambdas can be represented either with the greek letter (λ) or a backslash (\\ -
/// less aesthetic, but only one byte in size)
/// - the identifiers in `Classic` mode are `String`s of ASCII alphabetic characters
/// - `Classic` mode ignores whitespaces where unambiguous
/// - `DeBruijn` mode ignores all whitespaces (since indices > 15 are very unlikely)
/// - the indices in the `DeBruijn` notation mode start with 1 and are hexadecimal digits
///
/// # Example
/// ```
/// use lambda_calculus::parser::*;
/// use lambda_calculus::church::numerals::{succ, pred};
///
/// assert_eq!(parse(&"λn. λf. λx. n (λg. λh. h (g f)) (λu. x) (λu. u)", Classic), Ok(pred()));
/// assert_eq!(parse(&"λn.λf.λx.n(λg.λh.h(g f))(λu.x)(λu.u)", Classic), Ok(pred()));
///
/// assert_eq!(parse(  &"λλλ2(321)",  DeBruijn), Ok(succ()));
/// assert_eq!(parse(&r#"\\\2(321)"#, DeBruijn), Ok(succ()));
/// ```
pub fn parse(input: &str, notation: Notation) -> Result<Term, Error> {
    let tokens = if notation == DeBruijn {
        try!(tokenize_dbr(input))
    } else {
        convert_classic_tokens(&try!(tokenize_cla(input)))
    };
    let ast = try!(get_ast(&tokens));

    let exprs = try!(if let Sequence(exprs) = ast { Ok(exprs) } else { Err(InvalidExpression) });

    fold_exprs(&exprs)
}

fn fold_exprs(exprs: &[Expression]) -> Result<Term, Error> {
    let mut depth  = 0;
    let mut output = Vec::new();

    for expr in exprs.iter() {
        match *expr {
            Variable(i) => output.push(Var(i)),
            Abstraction => depth += 1,
            Sequence(ref exprs) => {
                let subexpr = try!(fold_exprs(exprs));
                output.push(subexpr)
            }
        }
    }

    let mut ret = try!(fold_terms(output));

    for _ in 0..depth {
        ret = abs(ret);
    }

    Ok(ret)
}

fn fold_terms(mut terms: Vec<Term>) -> Result<Term, Error> {
    if terms.len() > 1 {
        let fst = terms.remove(0);
        Ok( terms.into_iter().fold(fst, app) )
    } else if terms.len() == 1 {
        Ok( terms.pop().unwrap() ) // safe; ensured above
    } else {
        Err(EmptyExpression)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenization_error() {
        assert_eq!(tokenize_dbr(&"λλx2"),    Err(InvalidCharacter((3, 'x'))));
        assert_eq!(tokenize_cla(&"λa.λb a"), Err(InvalidCharacter((6, ' '))));
    }

    #[test]
    fn tokenization_success() {
        let quine = "λ 1 ( (λ 1 1) (λ λ λ λ λ 1 4 (3 (5 5) 2) ) ) 1";
        let tokens = tokenize_dbr(&quine);

        assert!(tokens.is_ok());
        assert_eq!(tokens.unwrap(), vec![Lambda, Number(1), Lparen, Lparen, Lambda, Number(1),
            Number(1), Rparen, Lparen, Lambda, Lambda, Lambda, Lambda, Lambda, Number(1),
            Number(4), Lparen, Number(3), Lparen, Number(5), Number(5), Rparen, Number(2),
            Rparen, Rparen, Rparen, Number(1)]);
    }

    #[test]
    fn tokenization_success_classic() {
        let blc_dbr = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))\
            (λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        let blc_cla = format!("{}", parse(&blc_dbr, DeBruijn).unwrap());

        let tokens_cla = tokenize_cla(&blc_cla);
        let tokens_dbr = tokenize_dbr(&blc_dbr);

        assert!(tokens_cla.is_ok());
        assert!(tokens_dbr.is_ok());

        assert_eq!(convert_classic_tokens(&tokens_cla.unwrap()), tokens_dbr.unwrap());
    }

    #[test]
    fn alternative_lambda_parsing() {
        assert_eq!(parse(&r#"\\\2(321)"#, DeBruijn), parse(&"λλλ2(321)", DeBruijn))
    }

    #[test]
    fn succ_ast() {
        let tokens = tokenize_dbr(&"λλλ2(321)").unwrap();
        let ast = get_ast(&tokens);

        assert_eq!(ast,
            Ok(Sequence(vec![
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
        ));
    }

    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        assert_eq!(parse(&y, DeBruijn).unwrap(),
            abs(
                app(
                    abs(app(Var(2), app(Var(1), Var(1)))),
                    abs(app(Var(2), app(Var(1), Var(1))))
                )
            )
        );
    }

    #[test]
    fn parse_quine() {
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";
        assert_eq!(parse(&quine, DeBruijn).unwrap(),
            abs(app(app(Var(1), app(abs(app(Var(1), Var(1))), abs(abs(abs(abs(abs(app(app(Var(1),
            Var(4)), app(app(Var(3), app(Var(5), Var(5))), Var(2)))))))))), Var(1)))
        );
    }

    #[test]
    fn parse_blc() {
        let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))\
                   (λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        assert_eq!(parse(&blc, DeBruijn).unwrap(),
            app(app(abs(app(Var(1), Var(1))), abs(abs(abs(app(app(app(Var(1),
            abs(abs(abs(abs(app(Var(3), abs(app(app(Var(5), app(Var(3), abs(app(app(Var(2),
            app(Var(3), abs(abs(app(Var(3), abs(app(app(Var(1), Var(2)), Var(3)))))))), app(Var(4),
            abs(app(Var(4), abs(app(app(Var(3), Var(1)), app(Var(2), Var(1))))))))))),
            app(app(Var(1), app(Var(2), abs(app(Var(1), Var(2))))), abs(app(app(Var(4),
            abs(app(Var(4), abs(app(Var(2), app(Var(1), Var(4))))))), Var(5)))))))))))),
            app(Var(3), Var(3))), Var(2)))))), abs(app(Var(1), app(abs(app(Var(1), Var(1))),
            abs(app(Var(1), Var(1)))))))
        );
    }
}
