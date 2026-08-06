extern crate lambda_calculus as lambda;

use lambda::combinators::{I, O};
use lambda::parser::{ParseError, parse_with_context};
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
fn eta_simple() {
    // λa. b a → b
    let mut expr = abs(app(Var(2), Var(1)));
    expr.eta(0);
    assert_eq!(expr, Var(1));

    // λa. a b → not η-reducible (rhs is not the binder)
    let mut expr = abs(app(Var(1), Var(2)));
    expr.eta(0);
    assert_eq!(expr, abs(app(Var(1), Var(2))));

    // λa. a a → not η-reducible (lhs uses the binder)
    let mut expr = abs(app(Var(1), Var(1)));
    expr.eta(0);
    assert_eq!(expr, abs(app(Var(1), Var(1))));
}

#[test]
fn eta_nested() {
    // λa. λb. a b → λa. a (inner η first, outer not η-reducible)
    let mut expr = abs(abs(app(Var(2), Var(1))));
    expr.eta(0);
    assert_eq!(expr, abs(Var(1)));

    // λa. λb. c a b → c (both levels η-reducible)
    let mut expr = abs(abs(app(app(Var(3), Var(2)), Var(1))));
    expr.eta(0);
    assert_eq!(expr, Var(1));
}

#[test]
fn eta_blocked() {
    // λa. a a → not η-reducible (lhs uses the binder)
    let mut expr = abs(app(Var(1), Var(1)));
    expr.eta(0);
    assert_eq!(expr, abs(app(Var(1), Var(1))));
    assert_eq!(expr.eta(0), 0);

    // λa. (λb. a b) a → inner λb. a b IS η-reducible (b not free in a)
    // giving λa. a a; then outer η on λa. a a is blocked (lhs uses binder)
    let mut expr = abs(app(abs(app(Var(2), Var(1))), Var(1)));
    expr.eta(0);
    assert_eq!(expr, abs(app(Var(1), Var(1))));
}

#[test]
fn eta_double_outer_inner() {
    // λa. (λb. c b) a → both inner (λb. c b → c) and outer (λa. c a → c) η reduce
    let mut expr = abs(app(abs(app(Var(3), Var(1))), Var(1)));
    expr.eta(0);
    assert_eq!(expr, Var(1));
    assert_eq!(expr.eta(0), 0);
}

#[test]
fn eta_identity_application() {
    // λa. (λb. b) a → λb. b
    let mut expr = abs(app(abs(Var(1)), Var(1)));
    expr.eta(0);
    assert_eq!(expr, abs(Var(1)));
}

#[test]
fn eta_free_function() {
    let ctx = Context::new(&["f"]);

    // λa. f a → f
    let mut expr = parse_with_context(&ctx, "λa. f a", Classic).unwrap();
    expr.eta(0);
    assert_eq!(expr, Var(1));

    // λa. λb. f a b → f
    let mut expr = parse_with_context(&ctx, "λa. λb. f a b", Classic).unwrap();
    expr.eta(0);
    assert_eq!(expr, Var(1));
}

#[test]
fn eta_with_limit() {
    let mut expr = abs(abs(app(Var(1), Var(1)))); // λa.λb. b
    let count = expr.eta(0);
    assert_eq!(count, 0); // not η-reducible

    // λa. λb. c a b → λa. λb. c a b with limit 0
    let mut expr = abs(abs(app(app(Var(3), Var(2)), Var(1))));
    let count = expr.eta(0);
    assert_eq!(count, 2); // both levels η-reduced
    assert_eq!(expr, Var(1));

    // λa. λb. c a b with limit 1 → only 1 reduction
    let mut expr = abs(abs(app(app(Var(3), Var(2)), Var(1))));
    let count = expr.eta(1);
    assert_eq!(count, 1); // inner η only
    assert_eq!(expr, abs(app(Var(2), Var(1)))); // λa. c a
}

#[test]
fn eta_free_function_beta() {
    let ctx = Context::new(&["f"]);

    // η-reduction via the free function
    let expr = parse_with_context(&ctx, "λa. λb. f a b", Classic).unwrap();
    let reduced = eta(expr, 0);
    assert_eq!(reduced, Var(1));

    // η-reduction with 0 limit but no reducible term
    let expr = abs(Var(1));
    let reduced = eta(expr, 0);
    assert_eq!(reduced, abs(Var(1)));
}

#[test]
#[ignore = "reserves gigabytes of stack and paints most of it"]
fn reduction_huge() {
    const MIB: usize = 1024 * 1024;

    // Measured peaks are ~221 MiB optimized and ~1.08 GiB unoptimized, so both knobs
    // are profile-dependent: an optimized run has no reason to pay for what the debug
    // build needs. The two are budgeted differently on purpose:
    //
    // - `stack_size` only reserves address space, and untouched pages stay free, so it
    //   is generous. Undershooting it is a SIGSEGV with no message.
    // - `paint_depth` memsets, so every painted byte becomes resident. It is the real
    //   cost and is kept tight. Undershooting it only saturates the reading, which the
    //   assertion below turns into a failure that says what to raise.
    const STACK_SIZE: usize = if cfg!(debug_assertions) {
        2048 * MIB
    } else {
        512 * MIB
    };
    const PAINT_DEPTH: usize = if cfg!(debug_assertions) {
        1280 * MIB
    } else {
        320 * MIB
    };

    let builder = thread::Builder::new()
        .name("reductor".into())
        .stack_size(STACK_SIZE);

    let factorial = parse("λ1(λλλ3(λ3(21))(λλ2(321)))(λλ2)(λλ21)(λλ21)", DeBruijn).unwrap();
    let church_ten = parse("λλ2(2(2(2(2(2(2(2(2(21)))))))))", DeBruijn).unwrap();

    let handler = builder
        .spawn(|| {
            // Painting is per-thread and only the owner may do it, so this has to run
            // on the reductor itself; the depth is process-wide configuration.
            assert!(
                stackler::Stackler::new().paint_depth(PAINT_DEPTH).install(),
                "the reductor's stack bounds could not be determined"
            );

            let (_, peak) = stackler::measure_peak(|| beta(app!(factorial, church_ten), HAP, 0));
            let peak = peak.expect("the reductor's stack could not be painted");

            assert!(
                !peak.is_saturated(),
                "{} bytes is only a lower bound; raise PAINT_DEPTH past {PAINT_DEPTH}",
                peak.bytes()
            );

            println!(
                "peak stack use: {} bytes ({:.2} MiB)",
                peak.bytes(),
                peak.bytes() as f64 / (1024.0 * 1024.0)
            );
        })
        .unwrap();

    handler.join().unwrap();
}
