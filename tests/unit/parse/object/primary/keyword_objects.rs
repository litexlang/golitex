//! Keyword-based primary object parser regressions.

use crate::parse::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_obj_line(source: &str) -> Result<Obj, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer.parse_blocks(source, Rc::from("test.lit"))?;
    assert_eq!(blocks.len(), 1, "{source:?}");
    Runtime::new().parse_obj(&mut blocks[0])
}

#[test]
fn primary_keyword_families_keep_their_ast_variants() {
    let cases = [
        ("gcd(12, 8)", ObjKind::Gcd),
        ("power_set(A)", ObjKind::PowerSet),
        ("finite_seq(R, 3)", ObjKind::FiniteSeqSet),
        ("matrix(R, 2, 3)", ObjKind::MatrixSet),
        ("general_cart(I, A, f)", ObjKind::GeneralCart),
        ("sum(1, n, f)", ObjKind::Sum),
        ("finite_set_product(A, f)", ObjKind::ProductOfFiniteSet),
        ("reduce(1, n, f, op, 0)", ObjKind::Reduce),
    ];

    for (source, expected_kind) in cases {
        let obj = parse_obj_line(source).expect("primary keyword object should parse");
        assert_eq!(obj.kind(), expected_kind, "{source}");
        assert_eq!(obj.to_string(), source, "{source}");
    }
}

#[test]
fn primary_keyword_arity_errors_remain_family_specific() {
    let cases = [
        ("gcd(1)", "gcd expects 2 arguments"),
        ("matrix(R, 2)", "matrix expects 3 arguments"),
        (
            "finite_set_product(A)",
            "finite_set_product expects 2 arguments (set, function)",
        ),
        (
            "reduce(1, n, f, op)",
            "reduce expects 5 arguments (start, end, function, operation, seed)",
        ),
    ];

    for (source, expected_message) in cases {
        let error = match parse_obj_line(source) {
            Ok(obj) => panic!("wrong-arity primary object parsed as {obj}"),
            Err(error) => error,
        };
        let RuntimeError::ParseError(error) = error else {
            panic!("expected parse error for {source}");
        };
        assert_eq!(error.msg, expected_message, "{source}");
    }
}

#[test]
fn parsed_sum_occurrences_are_present_and_distinct() {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(
            "sum(1, 3, fn(k Z) Z {k})\nsum(1, 3, fn(k Z) Z {k})",
            Rc::from("test.lit"),
        )
        .expect("two sum objects should tokenize");
    assert_eq!(blocks.len(), 2);

    let mut runtime = Runtime::new();
    let first = runtime
        .parse_obj(&mut blocks[0])
        .expect("first sum should parse");
    let second = runtime
        .parse_obj(&mut blocks[1])
        .expect("second sum should parse");

    let first_occurrence = first
        .source_occurrence_id()
        .expect("a parsed sum must own a source occurrence id");
    let second_occurrence = second
        .source_occurrence_id()
        .expect("a parsed sum must own a source occurrence id");
    assert_ne!(first_occurrence, second_occurrence);
    assert_eq!(obj_equality_key(&first), obj_equality_key(&second));
}
