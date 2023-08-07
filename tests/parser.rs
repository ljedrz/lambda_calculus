use lambda_calculus::{
    parse,
    parser::ParseError,
    term::Notation::{Classic, DeBruijn},
};

#[test]
fn parse_debruijn_and_classic() -> Result<(), ParseError> {
    for (dbr, cla) in [
        ("12", "a b"),
        ("λλ21", "λs. λz. s z"),
        (
            "λ2134(λ3215(λ4321)3215)2134",
            "λx. w x y z (λy. w x y z (λz. w x y z) w x y z) w x y z",
        ),
        (
            // See: http://alexandria.tue.nl/repository/freearticles/597619.pdf
            "λ2(λ421(5(λ4127)λ8))67",
            // the free variable list is ..ywzfba
            "λx. a (λt. b x t (f (λu. a u t z) λs. w)) w y",
        ),
        (
            // apply `plus zero one` to `s` and `z`
            "(λλλλ42(321))(λλ1)(λλ21)12",
            "(λm.λn.λs.λz. m s (n s z)) (λs.λz. z) (λs.λz. s z) s z",
        ),
    ] {
        let term_dbr = parse(dbr, DeBruijn)?;
        let term_cla = parse(cla, Classic)?;
        assert_eq!(term_dbr, term_cla);
    }
    Ok(())
}
