use crate::parsing::Tokenizer;
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
fn by_thm_parses_selection_and_legacy_bare_alias() {
    let selected =
        parse_one("by thm T(a) => not $P(a)").expect("parse by thm with selected atomic fact");
    let Stmt::By(ByStmt::ByThmStmt(selected)) = selected else {
        panic!("expected by thm statement")
    };
    assert!(!selected.selected_fact.has_positive_polarity());
    assert_eq!(selected.to_string(), "by thm T(a) => not $P(a)");

    let legacy = parse_one("by thm T(a)").expect("bare by thm should remain a legacy alias");
    let Stmt::ReleaseThmStmt(legacy) = legacy else {
        panic!("bare by thm should lower to release thm")
    };
    assert_eq!(legacy.to_string(), "release thm T(a)");
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
fn theorem_calls_preserve_bare_and_parenthesized_syntax() {
    let bare = parse_one("release thm direct_fact").expect("parse bare theorem call");
    let Stmt::ReleaseThmStmt(bare) = bare else {
        panic!("expected release thm statement")
    };
    assert!(bare.call.is_bare());
    assert!(bare.args().is_empty());
    assert_eq!(bare.to_string(), "release thm direct_fact");

    let parenthesized =
        parse_one("release thm zero_parameter_forall()").expect("parse empty argument list");
    let Stmt::ReleaseThmStmt(parenthesized) = parenthesized else {
        panic!("expected release thm statement")
    };
    assert!(!parenthesized.call.is_bare());
    assert!(parenthesized.args().is_empty());
    assert_eq!(
        parenthesized.to_string(),
        "release thm zero_parameter_forall()"
    );

    let selected =
        parse_one("by thm direct_fact => 1 = 1").expect("parse selected bare theorem call");
    let Stmt::By(ByStmt::ByThmStmt(selected)) = selected else {
        panic!("expected by thm statement")
    };
    assert!(selected.call.is_bare());
    assert_eq!(selected.to_string(), "by thm direct_fact => 1 = 1");

    let legacy = parse_one("by thm direct_fact").expect("parse legacy bare theorem call");
    let Stmt::ReleaseThmStmt(legacy) = legacy else {
        panic!("expected legacy by thm alias to lower to release thm")
    };
    assert!(legacy.call.is_bare());
    assert_eq!(legacy.to_string(), "release thm direct_fact");
}

#[test]
fn theorem_declarations_accept_claim_fact_shapes_except_forall_iff() {
    let cases = [
        ("thm atomic:\n    ? 1 = 1", "atomic"),
        ("thm conjunction:\n    ? 1 = 1 and 2 = 2", "and"),
        ("thm disjunction:\n    ? 1 = 1 or 2 = 3", "or"),
        ("thm chain:\n    ? 1 <= 1 = 1", "chain"),
        ("thm existence:\n    ? exist x R st {x = 0}", "exist"),
        (
            "thm negated_universal:\n    ? not forall x R:\n        x != x",
            "not forall",
        ),
        ("thm universal:\n    ? forall x R:\n        x = x", "forall"),
    ];
    for (source, expected_shape) in cases {
        let parsed = parse_one(source).unwrap_or_else(|error| {
            panic!("{expected_shape} theorem goal should parse: {error:?}")
        });
        let Stmt::Definition(DefinitionStmt::DefThmStmt(theorem)) = parsed else {
            panic!("{expected_shape}: expected theorem definition")
        };
        assert_eq!(
            match theorem.fact {
                Fact::AtomicFact(_) => "atomic",
                Fact::AndFact(_) => "and",
                Fact::OrFact(_) => "or",
                Fact::ChainFact(_) => "chain",
                Fact::ExistFact(_) => "exist",
                Fact::NotForall(_) => "not forall",
                Fact::ForallFact(_) => "forall",
                Fact::ForallFactWithIff(_) => "forall iff",
            },
            expected_shape
        );
    }

    let error = parse_one(
        "thm equivalence:\n    ? forall x R:\n        =>:\n            x = x\n        <=>:\n            x = x",
    )
    .expect_err("root forall iff theorem must remain rejected");
    assert!(error
        .trace_message()
        .contains("thm fact cannot be `forall ... <=>:`"));
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
            "by thm accepts either a bare legacy theorem call",
        ),
        (
            "by thm T(a):\n    ? $P(a)\n    1 = 1",
            "by thm accepts either a bare legacy theorem call",
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
