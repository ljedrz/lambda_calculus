extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::combinators::{I, O};
use std::thread;

#[test]
fn reduction_nor() {
    let reduces_instantly = parse(&"(λλ1)((λλλ((32)1))(λλ2))", DeBruijn).unwrap();
    assert_eq!(beta(reduces_instantly.clone(), NOR, 0),
               beta(reduces_instantly,         NOR, 1)
    );

    let should_reduce = parse(&"(λ2)((λ111)(λ111))", DeBruijn).unwrap();
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
#[ignore]
fn reduction_huge() {
    let builder = thread::Builder::new().name("reductor".into()).stack_size(1024 * 1024 * 1024);

    let factorial  = parse(&"λ1(λλλ3(λ3(21))(λλ2(321)))(λλ2)(λλ21)(λλ21)", DeBruijn).unwrap();
    let church_ten = parse(&"λλ2(2(2(2(2(2(2(2(2(21)))))))))", DeBruijn).unwrap();

    let handler = builder
        .spawn(|| { beta(app!(factorial, church_ten), HAP, 0); })
        .unwrap();

    handler.join().unwrap();
}
