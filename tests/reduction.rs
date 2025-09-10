extern crate lambda_calculus as lambda;

use lambda::combinators::{I, O};
use lambda::parser::{parse_with_context, ParseError};
use lambda::term::Context;
use lambda::*;
use std::thread;

#[test]
fn reduction_nor() {
    let reduces_instantly = parse("(λλ1)((λλλ((32)1))(λλ2))", DeBruijn).unwrap();
    assert_eq!(
        beta(reduces_instantly.clone(), NOR, 0),
        beta(reduces_instantly, NOR, 1)
    );

    let should_reduce = parse("(λ2)((λ111)(λ111))", DeBruijn).unwrap();
    assert_eq!(beta(should_reduce, NOR, 0), Var(1));

    let does_reduce = app(abs(Var(2)), O());
    assert_eq!(beta(does_reduce, NOR, 0), Var(1));
}

#[test]
fn reduction_cbn() {
    let mut expr = app(abs(app(I(), Var(1))), app(I(), I()));
    expr.reduce(CBN, 1);
    assert_eq!(expr, app(I(), app(I(), I())));
    expr.reduce(CBN, 1);
    assert_eq!(expr, app(I(), I()));
    expr.reduce(CBN, 1);
    assert_eq!(expr, I());
}

#[test]
fn reduction_app() {
    let mut wont_reduce = app(abs(Var(2)), O());
    wont_reduce.reduce(APP, 3);
    assert_eq!(wont_reduce, app(abs(Var(2)), O()));
}

#[test]
fn reduction_cbv() {
    let mut expr = app(abs(app(I(), Var(1))), app(I(), I()));
    expr.reduce(CBV, 1);
    assert_eq!(expr, app(abs(app(I(), Var(1))), I()));
    expr.reduce(CBV, 1);
    assert_eq!(expr, app(I(), I()));
    expr.reduce(CBV, 1);
    assert_eq!(expr, I());
}

#[test]
fn reduction_zero_plus_one() -> Result<(), ParseError> {
    let ctx = Context::new(&["s", "z"]);
    let mut expr = parse_with_context(
        &ctx,
        "(λm.λn.λs.λz. m s (n s z)) (λs.λz. z) (λs.λz. s z) s z",
        Classic,
    )?;
    expr.reduce(CBV, 2);
    assert_eq!(expr, parse("(λλ(λλ1)2((λλ21)21))12", DeBruijn)?);
    expr.reduce(CBV, 6);
    assert_eq!(expr, parse("12", DeBruijn)?);
    assert_eq!(expr.with_context(&ctx).to_string(), "s z");
    Ok(())
}

#[test]
#[ignore]
fn reduction_huge() {
    let builder = thread::Builder::new()
        .name("reductor".into())
        .stack_size(1024 * 1024 * 1024);

    let factorial = parse("λ1(λλλ3(λ3(21))(λλ2(321)))(λλ2)(λλ21)(λλ21)", DeBruijn).unwrap();
    let church_ten = parse("λλ2(2(2(2(2(2(2(2(2(21)))))))))", DeBruijn).unwrap();

    let handler = builder
        .spawn(|| {
            beta(app!(factorial, church_ten), HAP, 0);
        })
        .unwrap();

    handler.join().unwrap();
}
