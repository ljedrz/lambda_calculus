//! A parser for lambda expressions

use self::CToken::*;
use self::Expression::*;
use self::ParseError::*;
use self::Token::*;
use crate::term::Context;
pub use crate::term::Notation::*;
use crate::term::Term::*;
use crate::term::{abs, app, Notation, Term};
use std::error::Error;
use std::fmt;

/// An error returned by `parse()` when a parsing issue is encountered.
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    /// lexical error; contains the invalid character and its index
    InvalidCharacter((usize, char)),
    /// lexical error; an undefined free variable was found (classic notation only)
    UndefinedFreeVariable,
    /// syntax error; the expression is invalid
    InvalidExpression,
    /// syntax error; the expression is empty
    EmptyExpression,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseError::InvalidCharacter((idx, char)) => {
                write!(f, "lexical error; invalid character '{}' at {}", char, idx)
            }
            ParseError::UndefinedFreeVariable => {
                write!(f, "lexical error; an undefined free variable was used")
            }
            ParseError::InvalidExpression => write!(f, "syntax error; the expression is invalid"),
            ParseError::EmptyExpression => write!(f, "syntax error; the expression is empty"),
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
}

#[derive(Debug, PartialEq, Eq)]
#[doc(hidden)]
pub enum Token {
    /// the lambda symbol ('λ' or '\')
    Lambda,
    /// left parenthesis
    Lparen,
    /// right parenthesis
    Rparen,
    /// a hex-encoded digit
    Number(usize),
}

#[derive(Debug, PartialEq, Eq)]
#[doc(hidden)]
pub enum CToken {
    /// an abstraction with a bound variable
    CLambda(String),
    /// left parenthesis
    CLparen,
    /// right parenthesis
    CRparen,
    /// a variable with an identifier
    CName(String),
}

#[doc(hidden)]
pub fn tokenize_dbr(input: &str) -> Result<Vec<Token>, ParseError> {
    let chars = input.chars().enumerate();
    let mut tokens = Vec::with_capacity(input.len());

    for (i, c) in chars {
        match c {
            '\\' | 'λ' => tokens.push(Lambda),
            '(' => tokens.push(Lparen),
            ')' => tokens.push(Rparen),
            _ => {
                if let Some(n) = c.to_digit(16) {
                    tokens.push(Number(n as usize))
                } else if c.is_whitespace() {
                    // ignore
                } else {
                    return Err(InvalidCharacter((i, c)));
                }
            }
        }
    }

    Ok(tokens)
}

#[doc(hidden)]
pub fn tokenize_cla(input: &str) -> Result<Vec<CToken>, ParseError> {
    let mut chars = input.chars().enumerate().peekable();
    let mut tokens = Vec::with_capacity(input.len());

    while let Some((i, c)) = chars.next() {
        match c {
            '\\' | 'λ' => {
                let mut name = String::new();
                let mut first_char = true;
                for (i, c) in &mut chars {
                    if c == '.' {
                        break;
                    } else if first_char && c.is_alphabetic() {
                        first_char = false;
                        name.push(c);
                    } else if !first_char && c.is_alphanumeric() {
                        name.push(c);
                    } else {
                        return Err(InvalidCharacter((i, c)));
                    }
                }
                tokens.push(CLambda(name))
            }
            '(' => tokens.push(CLparen),
            ')' => tokens.push(CRparen),
            _ => {
                if c.is_whitespace() {
                    // ignore
                } else if c.is_alphabetic() {
                    let mut name = c.to_string();
                    while let Some(&(_, c)) = chars.peek() {
                        if c.is_whitespace() || c == '(' || c == ')' {
                            break;
                        } else {
                            name.push(c);
                            chars.next();
                        }
                    }
                    tokens.push(CName(name))
                } else {
                    return Err(InvalidCharacter((i, c)));
                }
            }
        }
    }

    Ok(tokens)
}

#[doc(hidden)]
pub fn convert_classic_tokens(ctx: &Context, tokens: &[CToken]) -> Result<Vec<Token>, ParseError> {
    let mut stack = Vec::with_capacity(tokens.len());
    stack.extend(ctx.iter().rev());
    _convert_classic_tokens(tokens, &mut stack, &mut 0)
}

fn _convert_classic_tokens<'t>(
    tokens: &'t [CToken],
    stack: &mut Vec<&'t str>,
    pos: &mut usize,
) -> Result<Vec<Token>, ParseError> {
    let mut output = Vec::with_capacity(tokens.len() - *pos);
    let mut inner_stack_count = 0;

    while let Some(token) = tokens.get(*pos) {
        match *token {
            CLambda(ref name) => {
                output.push(Lambda);
                stack.push(name);
                inner_stack_count += 1;
            }
            CLparen => {
                output.push(Lparen);
                *pos += 1;
                output.append(&mut _convert_classic_tokens(tokens, stack, pos)?);
            }
            CRparen => {
                output.push(Rparen);
                stack.truncate(stack.len() - inner_stack_count);
                return Ok(output);
            }
            CName(ref name) => {
                if let Some(index) = stack.iter().rev().position(|t| t == name) {
                    output.push(Number(index + 1))
                } else {
                    // a free variable not defined in the `Context`
                    return Err(UndefinedFreeVariable);
                }
            }
        }
        *pos += 1;
    }

    Ok(output)
}

#[derive(Debug, PartialEq)]
#[doc(hidden)]
pub enum Expression {
    /// an abstraction
    Abstraction,
    /// a sequence of `Expression`s
    Sequence(Vec<Expression>),
    /// a variable with a De Bruijn index
    Variable(usize),
}

#[doc(hidden)]
pub fn get_ast(tokens: &[Token]) -> Result<Expression, ParseError> {
    _get_ast(tokens, &mut 0)
}

fn _get_ast(tokens: &[Token], pos: &mut usize) -> Result<Expression, ParseError> {
    if tokens.is_empty() {
        return Err(EmptyExpression);
    }

    let mut expr = Vec::new();

    while let Some(token) = tokens.get(*pos) {
        match *token {
            Lambda => expr.push(Abstraction),
            Number(i) => expr.push(Variable(i)),
            Lparen => {
                *pos += 1;
                let subtree = _get_ast(tokens, pos)?;
                expr.push(subtree);
            }
            Rparen => return Ok(Sequence(expr)),
        }
        *pos += 1;
    }

    Ok(Sequence(expr))
}

/// Attempts to parse the input `&str` as a lambda `Term` encoded in the given `Notation`.
///
/// - lambdas can be represented either with the greek letter (λ) or a backslash (\\ -
///   less aesthetic, but only one byte in size)
/// - the identifiers in `Classic` notation are `String`s of alphabetic Unicode characters
/// - `Classic` notation ignores whitespaces where unambiguous
/// - the indices in the `DeBruijn` notation start with 1 and are hexadecimal digits
/// - `DeBruijn` notation ignores all whitespaces (since indices > 15 are very unlikely)
///
/// # Examples
/// ```
/// use lambda_calculus::*;
/// use lambda_calculus::combinators::{S, Y};
///
/// assert_eq!(parse(&"λf.(λx.f (x x)) (λx.f (x x))", Classic), Ok(Y()));
/// assert_eq!(parse(&"λƒ.(λℵ.ƒ(ℵ ℵ))(λℵ.ƒ(ℵ ℵ))", Classic),  Ok(Y()));
///
/// assert_eq!(parse(  &"λλλ31(21)",     DeBruijn), Ok(S()));
/// assert_eq!(parse(&r#"\\\3 1 (2 1)"#, DeBruijn), Ok(S()));
/// ```
///
/// # Errors
///
/// Returns a `ParseError` when a lexing or syntax error is encountered.
pub fn parse(input: &str, notation: Notation) -> Result<Term, ParseError> {
    parse_with_context(&Context::empty(), input, notation)
}

/// Attempts to parse the input `&str` using a provided context of free variables.
///
/// This function is identical to `parse()`, but it allows defining a set of named
/// free variables that are considered valid during parsing in `Classic` notation.
///
/// # Examples
/// ```
/// use lambda_calculus::{*, term::Context};
///
/// let ctx = Context::new(&["x", "y"]);
///
/// // `z` is not in the context, so it will be an error.
/// assert!(parse_with_context(&ctx, "z", Classic).is_err());
///
/// // `y` is in the context, so it's parsed as the outermost free variable (Var(2)).
/// assert_eq!(parse_with_context(&ctx, "y", Classic), Ok(Var(2)));
///
/// // In `λa.y`, `y` is still the outermost free variable, but its index is now 3.
/// assert_eq!(parse_with_context(&ctx, "λa.y", Classic), Ok(abs(Var(3))));
/// ```
///
/// # Errors
///
/// Returns a `ParseError` when a lexing or syntax error is encountered.
pub fn parse_with_context(
    ctx: &Context,
    input: &str,
    notation: Notation,
) -> Result<Term, ParseError> {
    let tokens = if notation == DeBruijn {
        tokenize_dbr(input)?
    } else {
        convert_classic_tokens(ctx, &tokenize_cla(input)?)?
    };
    let ast = get_ast(&tokens)?;

    let exprs = if let Sequence(exprs) = ast {
        Ok(exprs)
    } else {
        Err(InvalidExpression)
    };

    fold_exprs(&exprs?)
}

#[doc(hidden)]
pub fn fold_exprs(exprs: &[Expression]) -> Result<Term, ParseError> {
    let mut depth = 0;
    let mut output = Vec::new();

    for expr in exprs.iter() {
        match *expr {
            Abstraction => depth += 1,
            Variable(i) => output.push(Var(i)),
            Sequence(ref exprs) => output.push(fold_exprs(exprs)?),
        }
    }

    Ok(abs!(depth, fold_terms(output)?))
}

fn fold_terms(mut terms: Vec<Term>) -> Result<Term, ParseError> {
    if terms.is_empty() {
        Err(EmptyExpression)
    } else {
        let fst = terms.remove(0);
        if terms.is_empty() {
            Ok(fst)
        } else {
            Ok(terms.into_iter().fold(fst, app))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokenization_error() {
        assert_eq!(tokenize_dbr("λλx2"), Err(InvalidCharacter((2, 'x'))));
        assert_eq!(tokenize_cla("λa.λb a"), Err(InvalidCharacter((5, ' '))));
        assert_eq!(tokenize_cla("λa1.λb a1"), Err(InvalidCharacter((6, ' '))));
    }

    #[test]
    fn tokenization_success() {
        let quine = "λ 1 ( (λ 1 1) (λ λ λ λ λ 1 4 (3 (5 5) 2) ) ) 1";
        let tokens = tokenize_dbr(quine);

        assert!(tokens.is_ok());
        assert_eq!(
            tokens.unwrap(),
            vec![
                Lambda,
                Number(1),
                Lparen,
                Lparen,
                Lambda,
                Number(1),
                Number(1),
                Rparen,
                Lparen,
                Lambda,
                Lambda,
                Lambda,
                Lambda,
                Lambda,
                Number(1),
                Number(4),
                Lparen,
                Number(3),
                Lparen,
                Number(5),
                Number(5),
                Rparen,
                Number(2),
                Rparen,
                Rparen,
                Rparen,
                Number(1)
            ]
        );
    }

    #[test]
    fn tokenization_success_classic() {
        let blc_dbr = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))\
            (λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        let blc_cla = parse(blc_dbr, DeBruijn).unwrap().to_string();

        let tokens_cla = tokenize_cla(&blc_cla);
        let tokens_dbr = tokenize_dbr(blc_dbr);

        assert!(tokens_cla.is_ok());
        assert!(tokens_dbr.is_ok());

        assert_eq!(
            convert_classic_tokens(&Context::empty(), &tokens_cla.unwrap()).unwrap(),
            tokens_dbr.unwrap()
        );
    }

    #[test]
    fn tokenization_success_classic_with_free_variables() {
        let ctx = Context::new(&["a", "b"]);
        let blc_dbr = "12";
        let blc_cla = parse(blc_dbr, DeBruijn)
            .unwrap()
            .with_context(&ctx)
            .to_string();

        let tokens_cla = tokenize_cla(&blc_cla);
        let tokens_dbr = tokenize_dbr(blc_dbr);

        assert!(tokens_cla.is_ok());
        assert!(tokens_dbr.is_ok());

        assert_eq!(
            tokens_cla.and_then(|tokens| convert_classic_tokens(&ctx, &tokens)),
            tokens_dbr
        );
    }

    #[test]
    fn parse_classic_with_undefined_variable_error() {
        let ctx_with_y = Context::new(&["y"]);

        // "x" is not defined in the empty context
        assert_eq!(
            parse_with_context(&Context::empty(), "x", Classic),
            Err(UndefinedFreeVariable)
        );

        // "x" is not defined in this context either
        assert_eq!(
            parse_with_context(&ctx_with_y, "λz.x", Classic),
            Err(UndefinedFreeVariable)
        );

        // "y" is defined, so this should be OK
        assert!(parse_with_context(&ctx_with_y, "y", Classic).is_ok());
    }

    #[test]
    fn alternative_lambda_parsing() {
        assert_eq!(parse(r"\\\2(321)", DeBruijn), parse("λλλ2(321)", DeBruijn))
    }

    #[test]
    fn succ_ast() {
        let tokens = tokenize_dbr("λλλ2(321)").unwrap();
        let ast = get_ast(&tokens);

        assert_eq!(
            ast,
            Ok(Sequence(vec![
                Abstraction,
                Abstraction,
                Abstraction,
                Variable(2),
                Sequence(vec![Variable(3), Variable(2), Variable(1)])
            ]))
        );
    }

    #[test]
    fn parse_y() {
        let y = "λ(λ2(11))(λ2(11))";
        assert_eq!(
            parse(y, DeBruijn).unwrap(),
            abs(app(
                abs(app(Var(2), app(Var(1), Var(1)))),
                abs(app(Var(2), app(Var(1), Var(1))))
            ))
        );
    }

    #[test]
    fn parse_quine() {
        let quine = "λ1((λ11)(λλλλλ14(3(55)2)))1";
        assert_eq!(
            parse(quine, DeBruijn).unwrap(),
            abs(app(
                app(
                    Var(1),
                    app(
                        abs(app(Var(1), Var(1))),
                        abs!(
                            5,
                            app(
                                app(Var(1), Var(4)),
                                app(app(Var(3), app(Var(5), Var(5))), Var(2))
                            )
                        )
                    )
                ),
                Var(1)
            ))
        );
    }

    #[test]
    fn parse_blc() {
        let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))\
                   (λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
        assert_eq!(
            parse(blc, DeBruijn).unwrap(),
            app(
                app(
                    abs(app(Var(1), Var(1))),
                    abs!(
                        3,
                        app(
                            app(
                                app(
                                    Var(1),
                                    abs!(
                                        4,
                                        app(
                                            Var(3),
                                            abs(app(
                                                app(
                                                    Var(5),
                                                    app(
                                                        Var(3),
                                                        abs(app(
                                                            app(
                                                                Var(2),
                                                                app(
                                                                    Var(3),
                                                                    abs!(
                                                                        2,
                                                                        app(
                                                                            Var(3),
                                                                            abs(app(
                                                                                app(Var(1), Var(2)),
                                                                                Var(3)
                                                                            ))
                                                                        )
                                                                    )
                                                                )
                                                            ),
                                                            app(
                                                                Var(4),
                                                                abs(app(
                                                                    Var(4),
                                                                    abs(app(
                                                                        app(Var(3), Var(1)),
                                                                        app(Var(2), Var(1))
                                                                    ))
                                                                ))
                                                            )
                                                        ))
                                                    )
                                                ),
                                                app(
                                                    app(
                                                        Var(1),
                                                        app(Var(2), abs(app(Var(1), Var(2))))
                                                    ),
                                                    abs(app(
                                                        app(
                                                            Var(4),
                                                            abs(app(
                                                                Var(4),
                                                                abs(app(
                                                                    Var(2),
                                                                    app(Var(1), Var(4))
                                                                ))
                                                            ))
                                                        ),
                                                        Var(5)
                                                    ))
                                                )
                                            ))
                                        )
                                    )
                                ),
                                app(Var(3), Var(3))
                            ),
                            Var(2)
                        )
                    )
                ),
                abs(app(
                    Var(1),
                    app(abs(app(Var(1), Var(1))), abs(app(Var(1), Var(1))))
                ))
            )
        );
    }
}
