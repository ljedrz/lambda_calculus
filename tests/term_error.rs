extern crate lambda_calculus as lambda;

use lambda::term::Term;
use std::error::Error;

#[test]
fn term_error_question_mark_operator() {
    match using_question_mark_operator() {
        Result::Ok(_) => panic!("Should not be Ok"),
        Result::Err(e) => assert_eq!(e.to_string(), "the term is not an abstraction"),
    }
}

fn using_question_mark_operator() -> Result<(), Box<dyn Error>> {
    Term::Var(0).unabs()?;
    Ok(())
}
