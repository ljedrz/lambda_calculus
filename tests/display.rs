//! Regression tests for how `Display` names variables.
//!
//! Two bugs lived here. Free-variable names used to be generated eagerly, all
//! `max_free_index` of them, so printing a single-node term cost time and memory
//! proportional to its index rather than to the two characters of output. And the index
//! was narrowed to `u32` on the way in, so anything past `u32::MAX` either named the
//! wrong variable or tripped an `expect`.

extern crate lambda_calculus as lambda;

use lambda::term::Context;
use lambda::*;

/// A bare `Var(n + 1)` sits in a term of depth 0, so the name it is given is exactly the
/// generated name for ordinal `n`. That makes it a direct probe of the encoder.
fn name_of(ordinal: usize) -> String {
    Var(ordinal + 1).to_string()
}

#[test]
fn generated_names_are_bijective_base26() {
    // Pinned so the naming scheme cannot drift silently: every user-visible term
    // rendering depends on it.
    for (ordinal, expected) in [
        (0, "a"),
        (1, "b"),
        (25, "z"),
        (26, "aa"),
        (27, "ab"),
        (51, "az"),
        (52, "ba"),
        (701, "zz"),
        (702, "aaa"),
    ] {
        assert_eq!(name_of(ordinal), expected, "ordinal {ordinal}");
    }
}

#[test]
fn names_are_generated_on_demand() {
    // The point of this test is that it terminates at all. Naming every free variable up
    // to the index in advance would need ~1.8e19 allocations here.
    assert_eq!(Var(usize::MAX).to_string(), "gkgwbylwrxtlpo");

    // Likewise: one node, one short name, however large the index.
    assert_eq!(Var(4_000_001).to_string(), name_of(4_000_000));
    assert_eq!(Var(1_000_001).to_string().len(), 5);
}

#[test]
fn indices_past_u32_stay_distinct() {
    let boundary = 1usize << 32;

    // Narrowing to `u32` made this one panic outright, and made the next two collide
    // with the names of `Var(3)` and `Var(4)`.
    let at = Var(boundary).to_string();
    let past = Var(boundary + 3).to_string();
    let small = Var(3).to_string();
    let small_past = Var(4).to_string();

    assert_ne!(at, small);
    assert_ne!(past, small);
    assert_ne!(past, small_past);
    assert_ne!(at, past);

    // Consecutive indices must still get consecutive names across the boundary.
    assert_eq!(
        Var(u32::MAX as usize).to_string(),
        name_of(u32::MAX as usize - 1)
    );
    assert_eq!(Var(boundary).to_string(), name_of(boundary - 1));
    assert_eq!(Var(boundary + 1).to_string(), name_of(boundary));
}

#[test]
fn context_reports_unresolved_indices_faithfully() {
    let ctx = Context::new(&["x", "y", "z"]);

    assert_eq!(Var(3).with_context(&ctx).to_string(), "z");

    // The reported index used to be the truncated one, so everything past `u32::MAX`
    // claimed to be `<unknown4294967295>`.
    assert_eq!(
        Var(1usize << 32).with_context(&ctx).to_string(),
        "<unknown4294967296>"
    );
    assert_eq!(
        Var(usize::MAX).with_context(&ctx).to_string(),
        "<unknown18446744073709551615>"
    );
}

#[test]
fn binder_and_free_names_do_not_collide() {
    use lambda::term::LAMBDA;

    // Binders take the first `max_depth` names and free variables continue from there, so
    // a term mixing both must not reuse one. Built from `LAMBDA` so the expectation holds
    // under `backslash_lambda` too.
    let term = abs(abs(app(app(Var(1), Var(2)), app(Var(3), Var(4)))));
    assert_eq!(term.to_string(), format!("{LAMBDA}a.{LAMBDA}b.b a (c d)"));
}
