#[macro_use]
extern crate lambda_calculus as lambda;

use lambda::*;
use lambda::combinators::{I, O};
use std::thread;

#[test]
fn normal_order() {
    let reduces_instantly = parse(&"(λλ1)((λλλ((32)1))(λλ2))", DeBruijn).unwrap();
    assert_eq!(beta(reduces_instantly.clone(), NOR, 0, false),
               beta(reduces_instantly,         NOR, 1, false)
    );

    let should_reduce = parse(&"(λ2)((λ111)(λ111))", DeBruijn).unwrap();
    assert_eq!(beta(should_reduce, NOR, 0, false), Var(1));

    let does_reduce = app(abs(Var(2)), O());
    assert_eq!(beta(does_reduce, NOR, 0, false), Var(1));
}

#[test]
fn call_by_name_order() {
    let mut expr = app(abs(app(I(), Var(1))), app(I(), I()));
    expr.beta(CBN, 1, false);
    assert_eq!(expr, app(I(), app(I(), I())));
    expr.beta(CBN, 1, false);
    assert_eq!(expr, app(I(), I()));
    expr.beta(CBN, 1, false);
    assert_eq!(expr, I());
}

#[test]
fn applicative_order() {
    let mut wont_reduce = app(abs(Var(2)), O());
    wont_reduce.beta(APP, 3, false);
    assert_eq!(wont_reduce, app(abs(Var(2)), O()));
}

#[test]
fn call_by_value_order() {
    let mut expr = app(abs(app(I(), Var(1))), app(I(), I()));
    expr.beta(CBV, 1, false);
    assert_eq!(expr, app(abs(app(I(), Var(1))), I()));
    expr.beta(CBV, 1, false);
    assert_eq!(expr, app(I(), I()));
    expr.beta(CBV, 1, false);
    assert_eq!(expr, I());
}

#[test]
#[ignore]
fn huge_reduction() {
    let builder = thread::Builder::new().name("reductor".into()).stack_size(1024 * 1024 * 1024);

    let factorial  = parse(&"λ1(λλλ3(λ3(21))(λλ2(321)))(λλ2)(λλ21)(λλ21)", DeBruijn).unwrap();
    let church_ten = parse(&"λλ2(2(2(2(2(2(2(2(2(21)))))))))", DeBruijn).unwrap();

    let handler = builder
        .spawn(|| { beta(app!(factorial, church_ten), HAP, 0, false); })
        .unwrap();

    handler.join().unwrap();
}
