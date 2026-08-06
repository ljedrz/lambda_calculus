//! Stack-depth guards for the recursive operations on `Term`.
//!
//! A `Term` is a tree of `Box`es, so cloning, comparing, formatting, dropping and
//! reducing one all recurse once per nesting level. None of that is visible until a
//! term is deep enough to exhaust the stack, at which point the process dies on a
//! guard page with no unwinding, no panic message and no failing assertion.
//!
//! These tests put a number on the per-level cost so a change that makes any of
//! those paths deeper is caught here rather than as a mystery SIGSEGV in CI.
//!
//! The number worth remembering is the `Debug` one: `assert_eq!` formats both sides
//! with `Debug` when it fails, so a test comparing terms deeper than roughly a
//! thousand levels does not report a clean failure — it aborts while trying to
//! render one.

#![cfg(feature = "encoding")]

extern crate lambda_calculus as lambda;

use lambda::*;
use std::thread;

/// Nesting levels to measure over: deep enough that the per-level cost dominates
/// the fixed frame overhead, shallow enough to stay cheap.
const DEPTH: usize = 1000;

/// What libtest reserves for the thread it runs each test on. The ceilings below
/// are expressed against this, because it is the budget the rest of the suite has.
const LIBTEST_STACK: usize = 2 * 1024 * 1024;

/// Ceiling on what one nesting level may cost, in bytes.
///
/// The measured worst case is `Display` at ~800 B per level unoptimized (~190 B
/// optimized), so this catches a regression of about 2x without tripping on ordinary
/// codegen drift between compiler versions. Building a `String` per subterm rather
/// than writing into the `Formatter` used to put both formatting impls at 1.8-2.0 KiB,
/// which this would have caught.
const MAX_BYTES_PER_LEVEL: f64 = 1600.0;

/// `λa. (<inner> a)` nested `n` deep.
///
/// Built with a loop rather than recursion: recursing here would measure the
/// builder instead of the operation under test.
fn nest(n: usize) -> Term {
    let mut t = Var(1);
    for _ in 0..n {
        t = abs(app(t, Var(1)));
    }
    t
}

/// Runs `f` and returns its stack cost per nesting level.
fn per_level(name: &str, f: impl FnOnce()) -> f64 {
    let (_, peak) = stackler::measure_peak(f);
    let peak = peak.expect("the prober's stack could not be painted");

    assert!(
        !peak.is_saturated(),
        "{name}: {} bytes is only a lower bound; raise PAINT_DEPTH",
        peak.bytes()
    );

    let cost = peak.bytes() as f64 / DEPTH as f64;
    println!(
        "{name:18} {cost:>7.0} B/level  ->  at most {:>7.0} levels on libtest's {} MiB",
        LIBTEST_STACK as f64 / cost,
        LIBTEST_STACK / (1024 * 1024)
    );

    assert!(
        cost <= MAX_BYTES_PER_LEVEL,
        "{name} costs {cost:.0} B per nesting level, over the {MAX_BYTES_PER_LEVEL:.0} B \
         ceiling: terms deeper than {:.0} levels now overflow libtest's {} MiB stack",
        LIBTEST_STACK as f64 / cost,
        LIBTEST_STACK / (1024 * 1024)
    );

    cost
}

#[test]
fn recursive_term_ops_stay_shallow() {
    const MIB: usize = 1024 * 1024;

    // Room for `DEPTH` levels at the ceiling above, with margin. Reserved address
    // space is free until touched; only the paint below becomes resident.
    const STACK_SIZE: usize = 64 * MIB;
    const PAINT_DEPTH: usize = 32 * MIB;

    let prober = thread::Builder::new()
        .name("prober".into())
        .stack_size(STACK_SIZE)
        .spawn(|| {
            // Only the thread that owns a stack may paint it, so this runs here
            // rather than on the caller.
            assert!(
                stackler::Stackler::new().paint_depth(PAINT_DEPTH).install(),
                "the prober's stack bounds could not be determined"
            );

            println!("over {DEPTH} nested levels:\n");

            let subject = nest(DEPTH);

            per_level("clone", || {
                std::hint::black_box(subject.clone());
            });
            per_level("PartialEq", || {
                std::hint::black_box(subject == subject.clone());
            });
            per_level("Display", || {
                std::hint::black_box(subject.to_string().len());
            });
            let debug = per_level("Debug", || {
                std::hint::black_box(format!("{subject:?}").len());
            });
            per_level("beta NOR", || {
                std::hint::black_box(beta(subject.clone(), NOR, 1));
            });
            per_level("eta", || {
                std::hint::black_box(eta(subject.clone(), 1));
            });

            let owned = nest(DEPTH);
            per_level("drop", move || drop(owned));

            // `Debug` is the deepest path and the one `assert_eq!` takes on failure,
            // so it is what actually bounds how deep a term a test may compare.
            println!(
                "\nassert_eq! on terms deeper than ~{:.0} levels aborts instead of failing",
                LIBTEST_STACK as f64 / debug
            );
        })
        .unwrap();

    prober.join().unwrap();
}

/// The terms the rest of the suite builds are nowhere near the ceiling above; this
/// pins that down so a new test that quietly reduces something enormous is noticed.
#[test]
fn representative_workloads_are_far_from_the_limit() {
    use lambda::data::num::church;

    const PAINT_DEPTH: usize = 8 * 1024 * 1024;

    assert!(
        stackler::Stackler::new().paint_depth(PAINT_DEPTH).install(),
        "the test thread's stack bounds could not be determined"
    );

    // The heaviest thing the suite does: `fac 5` under normal order.
    let (_, peak) = stackler::measure_peak(|| {
        std::hint::black_box(beta(app(church::fac(), 5.into_church()), NOR, 0));
    });
    let peak = peak.expect("the test thread's stack could not be painted");

    println!(
        "church::fac 5 NOR: {} B ({:.1}% of libtest's {} MiB)",
        peak.bytes(),
        100.0 * peak.bytes() as f64 / LIBTEST_STACK as f64,
        LIBTEST_STACK / (1024 * 1024)
    );

    // Measured at ~71 KiB unoptimized, i.e. about 3.5% of the budget. A tenth of the
    // stack leaves generous room for drift while still catching a step change.
    assert!(
        peak.bytes() < LIBTEST_STACK / 10,
        "fac 5 now uses {} bytes, over a tenth of libtest's {} MiB stack",
        peak.bytes(),
        LIBTEST_STACK / (1024 * 1024)
    );
}
