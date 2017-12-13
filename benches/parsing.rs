#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::parser::*;
use lambda::parser::Token::*;
use lambda::parser::Expression::*;

#[bench]
fn parser_tokenizing_dbr(b: &mut Bencher) {
    let blc_debruijn = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))\
        (1(2(λ12))(λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";

    b.iter(|| { let _ = tokenize_dbr(&blc_debruijn); } );
}

#[bench]
fn parser_tokenizing_cla(b: &mut Bencher) {
    let blc_classic = "(λa.a a) (λa.λb.λc.c (λd.λe.λf.λg.e (λh.d (f (λi.h (g (λj.λk.i (λl.l k j)))\
     (f (λj.g (λk.i k (j k)))))) (h (g (λi.i h)) (λi.f (λj.g (λk.j (k h))) e)))) (a a) b)\
     (λa.a ((λb.b b) (λb.b b)))";

    b.iter(|| { convert_classic_tokens(&tokenize_cla(&blc_classic).unwrap()); } );
}

#[bench]
fn parser_creating_ast(b: &mut Bencher) {
    let blc_tokens = vec![Lparen, Lambda, Number(1), Number(1), Rparen, Lparen, Lambda, Lambda,
        Lambda, Number(1), Lparen, Lambda, Lambda, Lambda, Lambda, Number(3), Lparen, Lambda,
        Number(5), Lparen, Number(3), Lparen, Lambda, Number(2), Lparen, Number(3), Lparen, Lambda,
        Lambda, Number(3), Lparen, Lambda, Number(1), Number(2), Number(3), Rparen, Rparen, Rparen,
        Lparen, Number(4), Lparen, Lambda, Number(4), Lparen, Lambda, Number(3), Number(1), Lparen,
        Number(2), Number(1), Rparen, Rparen, Rparen, Rparen, Rparen, Rparen, Lparen, Number(1),
        Lparen, Number(2), Lparen, Lambda, Number(1), Number(2), Rparen, Rparen, Lparen, Lambda,
        Number(4), Lparen, Lambda, Number(4), Lparen, Lambda, Number(2), Lparen, Number(1),
        Number(4), Rparen, Rparen, Rparen, Number(5), Rparen, Rparen, Rparen, Rparen, Lparen,
        Number(3), Number(3), Rparen, Number(2), Rparen, Lparen, Lambda, Number(1), Lparen, Lparen,
        Lambda, Number(1), Number(1), Rparen, Lparen, Lambda, Number(1), Number(1), Rparen, Rparen,
        Rparen];

    b.iter(|| { let _ = get_ast(&blc_tokens); } );
}

#[bench]
fn parser_interpreting_ast(b: &mut Bencher) {
    let blc_ast = vec![Sequence(vec![Abstraction, Variable(1), Variable(1)]), Sequence(vec![Abstraction,
        Abstraction, Abstraction, Variable(1), Sequence(vec![Abstraction, Abstraction, Abstraction,
        Abstraction, Variable(3), Sequence(vec![Abstraction, Variable(5), Sequence(vec![Variable(3),
        Sequence(vec![Abstraction, Variable(2), Sequence(vec![Variable(3), Sequence(vec![Abstraction,
        Abstraction, Variable(3), Sequence(vec![Abstraction, Variable(1), Variable(2), Variable(3)])])]),
        Sequence(vec![Variable(4), Sequence(vec![Abstraction, Variable(4), Sequence(vec![Abstraction,
        Variable(3), Variable(1), Sequence(vec![Variable(2), Variable(1)])])])])])]),
        Sequence(vec![Variable(1), Sequence(vec![Variable(2), Sequence(vec![Abstraction, Variable(1),
        Variable(2)])]), Sequence(vec![Abstraction, Variable(4), Sequence(vec![Abstraction, Variable(4),
        Sequence(vec![Abstraction, Variable(2), Sequence(vec![Variable(1), Variable(4)])])]),
        Variable(5)])])])]), Sequence(vec![Variable(3), Variable(3)]), Variable(2)]),
        Sequence(vec![Abstraction, Variable(1), Sequence(vec![Sequence(vec![Abstraction, Variable(1),
        Variable(1)]), Sequence(vec![Abstraction, Variable(1), Variable(1)])])])];

    b.iter(|| { let _ = fold_exprs(&blc_ast); } );
}
