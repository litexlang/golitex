use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_one(source: &str) -> Result<Stmt, RuntimeError> {
    let mut runtime = Runtime::default();
    let mut blocks = Tokenizer::new()
        .parse_blocks(source, Rc::from("by_thm_selected_fact_test.lit"))
        .expect("tokenize by thm statement");
    assert_eq!(blocks.len(), 1);
    runtime.parse_statement(&mut blocks[0])
}

#[test]
fn by_thm_requires_and_parses_one_selected_atomic_fact() {
    let selected =
        parse_one("by thm T(a) => not $P(a)").expect("parse by thm with selected atomic fact");
    let Stmt::By(ByStmt::ByThmStmt(selected)) = selected else {
        panic!("expected by thm statement")
    };
    assert!(!selected.selected_fact.has_positive_polarity());
    assert_eq!(selected.to_string(), "by thm T(a) => not $P(a)");

    let error = parse_one("by thm T(a)").expect_err("bare by thm should fail");
    let RuntimeError::ParseError(error) = error else {
        panic!("expected parse error")
    };
    assert!(error.msg.contains("use `release thm name(args)`"));
}

#[test]
fn release_thm_parses_as_its_own_statement_and_rejects_selection_or_proof_bodies() {
    let released = parse_one("release thm T(a)").expect("parse release thm");
    let Stmt::ReleaseThmStmt(released) = released else {
        panic!("expected release thm statement")
    };
    assert_eq!(released.to_string(), "release thm T(a)");

    for source in [
        "release thm T(a) => $P(a)",
        "release thm T(a):\n    ? $P(a)",
    ] {
        let error = parse_one(source).expect_err("non-bare release thm should fail");
        let RuntimeError::ParseError(error) = error else {
            panic!("{source}: expected parse error")
        };
        assert!(
            error
                .msg
                .contains("release thm accepts only a bare theorem call"),
            "{source}: {}",
            error.msg
        );
    }

    let error = parse_one("release claim T(a)").expect_err("non-thm release should fail");
    let RuntimeError::ParseError(error) = error else {
        panic!("expected parse error")
    };
    assert_eq!(error.msg, "release: expected `thm name(args)`");
}

#[test]
fn by_thm_selected_fact_rejects_missing_compound_and_indented_targets() {
    let cases = [
        ("by thm T(a) =>", "by thm: `=>` expects one atomic fact"),
        (
            "by thm T(a) => $P(a) and $Q(a)",
            "by thm: `=>` expects exactly one atomic fact",
        ),
        (
            "by thm T(a):\n    1 = 1",
            "by thm requires `=>` followed by one selected atomic fact",
        ),
        (
            "by thm T(a):\n    ? $P(a)\n    1 = 1",
            "by thm requires `=>` followed by one selected atomic fact",
        ),
    ];
    for (source, expected) in cases {
        let error = parse_one(source).expect_err("invalid by thm target should fail");
        let RuntimeError::ParseError(error) = error else {
            panic!("{source}: expected parse error")
        };
        assert!(error.msg.contains(expected), "{source}: {}", error.msg);
    }
}
