//! [Standard terms](https://en.wikipedia.org/wiki/Lambda_calculus#Standard_terms)
//!
//! * [SKI](https://en.wikipedia.org/wiki/SKI_combinator_calculus)
//! * [Iota](https://en.wikipedia.org/wiki/Iota_and_Jot)
//! * [BCKW](https://en.wikipedia.org/wiki/B,_C,_K,_W_system)
// //! * the recursion combinator U - needs more research
//! * the looping combinator ω
//! * the divergent combinator Ω
//! * [the fixed-point combinator Y](https://en.wikipedia.org/wiki/Fixed-point_combinator)

use term::*;
use term::Term::*;

/// I - the identity combinator.
///
/// I := λx.x = λ 1
pub fn i() -> Term { abs(Var(1)) }

/// K - the constant / discarding combinator.
///
/// K := λxy.x = λ λ 2 = true
pub fn k() -> Term { abs(abs(Var(2))) }

/// S - the substitution combinator.
///
/// S := λxyz.x z (y z) = λ λ λ 3 1 (2 1)
pub fn s() -> Term { abs(abs(abs(Var(3).app(Var(1)).app(Var(2).app(Var(1)))))) }

/// X - the Iota combinator.
///
/// X := λx.x S K = λ 1 S K
pub fn x() -> Term { abs(Var(1).app(k()).app(s())) }

/// B - the composition combinator.
///
/// B := λxyz.x (y z) = λ λ λ 3 (2 1)
pub fn b() -> Term { abs(abs(abs(Var(3).app(Var(2).app(Var(1)))))) }

/// C - the swapping combinator.
///
/// C := λxyz.x z y = λ λ λ 3 1 2
pub fn c() -> Term { abs(abs(abs(Var(3).app(Var(1)).app(Var(2))))) }

/// W - the duplicating combinator.
///
/// W := λxy.x y y = λ λ 2 1 1
pub fn w() -> Term { abs(abs(Var(2).app(Var(1)).app(Var(1)))) }
/*
/// U - the recursion combinator.
///
/// U := λxy.y (x x y) = λ λ 1 (2 2 1)
pub fn u() -> Term { abs(abs(Var(1).app(Var(2).app(Var(2)).app(Var(1))))) }
*/
/// ω - the looping combinator.
///
/// ω := λx.x x
pub fn om() -> Term { abs(Var(1).app(Var(1))) }

/// Ω - the divergent combinator.
///
/// Ω := ω ω
pub fn omm() -> Term { om().app(om()) }

/// Y - the fixed-point combinator.
///
/// Y := λg.(λx.g (x x)) (λx.g (x x)) = λ (λ 2 (1 1)) (λ 2 (1 1))
pub fn y() -> Term { abs(app(abs(Var(2).app(Var(1).app(Var(1)))), abs(Var(2).app(Var(1).app(Var(1)))))) }

