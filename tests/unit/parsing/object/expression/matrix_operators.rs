//! Matrix-operator object parser regressions.

use crate::parsing::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_obj_line(source: &str) -> Result<Obj, RuntimeError> {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer.parse_blocks(source, Rc::from("test.lit"))?;
    assert_eq!(blocks.len(), 1, "{source:?}");
    Runtime::default().parse_obj(&mut blocks[0])
}

#[test]
fn unicode_set_operators_have_canonical_ast_and_precedence() {
    let cases = [
        ("A ∪ B ∩ C", "union(A, intersect(B, C))"),
        ("A ∩ B ∪ C", "union(intersect(A, B), C)"),
        ("A × B × C", "cart(A, B, C)"),
        ("A ∪ B × C", "union(A, cart(B, C))"),
        ("(A ∪ B) ∩ C", "intersect(union(A, B), C)"),
    ];

    for (source, canonical) in cases {
        let obj = parse_obj_line(source).expect("Unicode set expression should parse");
        assert_eq!(obj.to_string(), canonical, "{source}");
    }

    let product = parse_obj_line("2 × 3").expect("Cartesian product syntax should parse");
    assert_eq!(product.kind(), ObjKind::Cart);
    assert_eq!(product.to_string(), "cart(2, 3)");
}

#[test]
fn apostrophe_matrix_operators_keep_existing_ast_variants() {
    let cases = [
        ("A '+ B", ObjKind::MatrixAdd),
        ("A '- B", ObjKind::MatrixSub),
        ("A '* B", ObjKind::MatrixMul),
        ("3 *' A", ObjKind::MatrixScalarMul),
        ("A '^ 2", ObjKind::MatrixPow),
    ];

    for (source, expected_kind) in cases {
        let obj = parse_obj_line(source).expect("matrix operator should parse");
        assert_eq!(obj.kind(), expected_kind, "{source}");
        assert_eq!(obj.to_string(), source, "{source}");
    }

    let interval = parse_obj_line("'(0, 1)").expect("interval literal should still parse");
    assert_eq!(interval.kind(), ObjKind::IntervalObj);
    assert_eq!(interval.to_string(), "'(0, 1)");
}

#[test]
fn big_set_family_operators_parse_and_print_canonically() {
    let cases = [
        ("big_union(F)", ObjKind::BigUnion),
        ("big_intersect(F)", ObjKind::BigIntersect),
        ("index_union(I, X, A)", ObjKind::IndexUnion),
        ("index_intersect(I, X, A)", ObjKind::IndexIntersect),
    ];

    for (source, expected_kind) in cases {
        let obj = parse_obj_line(source).expect("set-family operator should parse");
        assert_eq!(obj.kind(), expected_kind, "{source}");
        assert_eq!(obj.to_string(), source, "{source}");
    }

    assert_eq!(ObjKind::BigUnion as u8, 18);
    assert_eq!(ObjKind::BigIntersect as u8, 19);
    assert_eq!(ObjKind::IndexUnion as u8, 93);
    assert_eq!(ObjKind::IndexIntersect as u8, 94);
}

#[test]
fn removed_set_diff_name_is_reclaimed_by_generic_function_parser() {
    let obj = parse_obj_line("set_diff(A, B)")
        .expect("removed set_diff spelling should remain syntactically available");
    assert_eq!(obj.kind(), ObjKind::FnObj);
    assert_eq!(obj.to_string(), "set_diff(A, B)");
}

#[test]
fn native_scalar_syntax_has_dedicated_ast_nodes() {
    let cases = [
        ("i", ObjKind::ImaginaryUnit),
        ("e", ObjKind::EulerNumber),
        ("pi", ObjKind::Pi),
        ("re(i)", ObjKind::RealPart),
        ("img(i)", ObjKind::ImaginaryPart),
        ("C_abs(i)", ObjKind::ComplexAbs),
    ];

    for (source, expected_kind) in cases {
        let obj = parse_obj_line(source).expect("native scalar syntax should parse");
        assert_eq!(obj.kind(), expected_kind, "{source}");
        assert_eq!(obj.to_string(), source, "{source}");
    }

    assert_eq!(ObjKind::EulerNumber as u8, 74);
    assert_eq!(ObjKind::Pi as u8, 75);
}

#[test]
fn big_set_family_operators_reject_wrong_arity() {
    let cases = [
        ("big_union(A, B)", "big_union expects 1 argument"),
        ("big_intersect(A, B)", "big_intersect expects 1 argument"),
        (
            "index_union(I, X)",
            "index_union expects 3 arguments (index set, ambient set, family function)",
        ),
        (
            "index_intersect(I, X, A, B)",
            "index_intersect expects 3 arguments (index set, ambient set, family function)",
        ),
    ];

    for (source, expected_message) in cases {
        let error = match parse_obj_line(source) {
            Ok(obj) => panic!("wrong-arity set-family operator parsed as {obj}"),
            Err(error) => error,
        };
        let RuntimeError::ParseError(error) = error else {
            panic!("expected parse error for {source}");
        };
        assert_eq!(error.msg, expected_message);
    }
}
