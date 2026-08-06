//! `fmt::Debug` and `parse(.., DeBruijn)` must be exact inverses.
//!
//! They were not. De Bruijn notation is concatenative - adjacent digits are an
//! application, not a multi-digit number - so an index above `F` used to render as
//! several characters and read back as something else. `Var(16)` printed as `10` and
//! reparsed as `App(Var(1), Var(0))`; `Var(17)` printed as `11` and reparsed as
//! `App(Var(1), Var(1))`, whose own rendering is *also* `11`, so the corruption was a
//! fixed point and completely silent.
//!
//! Indices that do not fit in one hex digit are now written `[n]` in decimal.

extern crate lambda_calculus as lambda;

use lambda::*;

/// Asserts that `term` survives a trip through its own `Debug` rendering.
fn assert_roundtrips(term: &Term) {
    let rendered = format!("{term:?}");
    match parse(&rendered, DeBruijn) {
        Ok(back) => assert_eq!(
            back, *term,
            "{rendered} reparsed as {back:?} instead of {term:?}"
        ),
        Err(e) => panic!("{rendered} failed to reparse: {e:?}"),
    }
}

#[test]
fn every_index_roundtrips() {
    // Exhaustive across the single-digit boundary and well past it, including 0, which
    // renders as `[0]` in De Bruijn notation and used to be an unparseable `undefined`.
    for i in 0..5_000 {
        assert_roundtrips(&Var(i));
        assert_roundtrips(&abs(Var(i)));
        assert_roundtrips(&app(Var(i), Var(1)));
        assert_roundtrips(&app(Var(1), Var(i)));
    }

    for i in [usize::MAX, usize::MAX - 1, 1 << 32, 1 << 63, 1_000_000] {
        assert_roundtrips(&Var(i));
        assert_roundtrips(&abs(app(Var(i), Var(i))));
    }
}

#[test]
fn the_historical_collisions_are_gone() {
    // Each of these used to render as a string that parsed to the term on the right.
    assert_ne!(
        format!("{:?}", Var(16)),
        format!("{:?}", app(Var(1), Var(0)))
    );
    assert_ne!(
        format!("{:?}", Var(17)),
        format!("{:?}", app(Var(1), Var(1)))
    );
    assert_ne!(
        format!("{:?}", Var(32)),
        format!("{:?}", app(Var(2), Var(0)))
    );
    assert_ne!(
        format!("{:?}", Var(31)),
        format!("{:?}", app(Var(1), Var(15)))
    );

    // The specific rendering, pinned. Digits inside the brackets are hexadecimal, exactly
    // as they are outside: the brackets delimit, they do not switch base.
    assert_eq!(format!("{:?}", Var(15)), "F");
    assert_eq!(format!("{:?}", Var(16)), "[10]");
    assert_eq!(format!("{:?}", Var(300)), "[12C]");
    assert_eq!(format!("{:?}", UD), "[0]");

    // `Display` is human-facing and still spells the sentinel out.
    assert_eq!(UD.to_string(), "undefined");
}

#[test]
fn existing_notation_is_unchanged() {
    // Every term expressible before must render exactly as it did, so saved strings and
    // documentation stay valid. Indices 1..=15 are the whole of that range.
    for (rendered, expected) in [
        ("λλ1", abs(abs(Var(1)))),
        (
            "λλλ2(321)",
            abs(abs(abs(app(Var(2), app!(Var(3), Var(2), Var(1)))))),
        ),
        (
            "λλλ31(21)",
            abs(abs(abs(app!(Var(3), Var(1), app(Var(2), Var(1)))))),
        ),
    ] {
        assert_eq!(parse(rendered, DeBruijn).unwrap(), expected);
        // Normalised so the expectation holds under `backslash_lambda`, which makes
        // `LAMBDA` a backslash. The parser accepts both characters regardless.
        assert_eq!(
            format!("{expected:?}").replace(lambda::term::LAMBDA, "λ"),
            rendered
        );
    }

    // Lowercase hex digits still mean what they always did.
    assert_eq!(
        parse("λλ2a1", DeBruijn).unwrap(),
        parse("λλ2A1", DeBruijn).unwrap()
    );
    assert_eq!(parse("A", DeBruijn).unwrap(), Var(10));
    assert_eq!(parse("F", DeBruijn).unwrap(), Var(15));
}

#[test]
fn brackets_delimit_without_switching_base() {
    // The digits inside are hexadecimal, so a bracketed index and the bare form of the
    // same index agree. If the brackets held decimal instead, `[10]` would be `A`.
    assert_eq!(parse("[A]", DeBruijn).unwrap(), Var(10));
    assert_eq!(
        parse("[A]", DeBruijn).unwrap(),
        parse("A", DeBruijn).unwrap()
    );
    assert_eq!(parse("[a]", DeBruijn).unwrap(), Var(10));
    assert_eq!(parse("[F]", DeBruijn).unwrap(), Var(15));
    assert_eq!(parse("[10]", DeBruijn).unwrap(), Var(16));
    assert_eq!(parse("[12C]", DeBruijn).unwrap(), Var(300));

    // Accepted even where a bare digit would do, so the form is easy to write by hand.
    assert_eq!(parse("[1]", DeBruijn).unwrap(), Var(1));
    assert_eq!(parse("[0]", DeBruijn).unwrap(), UD);
    assert_eq!(
        parse("λλ[2][1]", DeBruijn).unwrap(),
        abs(abs(app(Var(2), Var(1))))
    );
    assert_eq!(
        parse("λλ21", DeBruijn).unwrap(),
        parse("λλ[2][1]", DeBruijn).unwrap()
    );

    // A bracketed index is one token, so `[10]` and `10` are different terms.
    assert_ne!(
        parse("[10]", DeBruijn).unwrap(),
        parse("10", DeBruijn).unwrap()
    );
    assert_eq!(parse("10", DeBruijn).unwrap(), app(Var(1), UD));
    assert_eq!(parse("16", DeBruijn).unwrap(), app(Var(1), Var(6)));
}

#[test]
fn malformed_brackets_are_rejected_not_panics() {
    for bad in [
        "[",
        "]",
        "[]",
        // `G` is not a hex digit, inside brackets or out.
        "[G]",
        "[1G]",
        "[1",
        "λ[",
        "[[1]]",
        "[1]]",
        "[-1]",
        // Whitespace is ignored between tokens but may not split an index.
        "[ ]",
        "[1 ]",
        // Too large to hold in a `usize`, which is 16 hex digits.
        "[FFFFFFFFFFFFFFFFF]",
    ] {
        assert!(
            parse(bad, DeBruijn).is_err(),
            "{bad:?} should not have parsed"
        );
    }
}

#[test]
fn random_terms_roundtrip() {
    // Deterministic LCG: no dependency, and a failure is reproducible.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0 >> 33
        }
    }

    fn build(rng: &mut Rng, budget: u32) -> Term {
        // Indices deliberately straddle the single-digit boundary at 15.
        if budget == 0 {
            return Var((rng.next() % 64) as usize);
        }
        match rng.next() % 3 {
            0 => Var((rng.next() % 64) as usize),
            1 => abs(build(rng, budget - 1)),
            _ => app(build(rng, budget - 1), build(rng, budget - 1)),
        }
    }

    let mut rng = Rng(0x5eed);
    for i in 0..20_000 {
        assert_roundtrips(&build(&mut rng, 1 + (i % 8) as u32));
    }
}
