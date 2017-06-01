#![feature(test)]
extern crate test;

extern crate lambda_calculus as lambda;

use test::Bencher;
use lambda::parser::*;

#[bench]
fn parsing_debruijn(b: &mut Bencher) {
    let blc = "(λ11)(λλλ1(λλλλ3(λ5(3(λ2(3(λλ3(λ123)))(4(λ4(λ31(21))))))(1(2(λ12))\
        (λ4(λ4(λ2(14)))5))))(33)2)(λ1((λ11)(λ11)))";
    b.iter(|| { let _ = parse(&blc, DeBruijn); } );
}

#[bench]
fn parsing_classic(b: &mut Bencher) {
    let blc = "(λa.a a) (λa.λb.λc.c (λd.λe.λf.λg.e (λh.d (f (λi.h (g (λj.λk.i (λl.l k j)))\
     (f (λj.g (λk.i k (j k)))))) (h (g (λi.i h)) (λi.f (λj.g (λk.j (k h))) e)))) (a a) b)\
      (λa.a ((λb.b b) (λb.b b)))";
    b.iter(|| { let _ = parse(&blc, Classic); } );
}
