//! Arithmetic precedence parser regressions.

use crate::parsing::Tokenizer;
use crate::prelude::*;
use std::rc::Rc;

fn parse_obj_line(source: &str) -> Obj {
    let tokenizer = Tokenizer::new();
    let mut blocks = tokenizer
        .parse_blocks(source, Rc::from("test.lit"))
        .expect("tokenize object line");
    assert_eq!(blocks.len(), 1, "{source:?}");
    Runtime::default()
        .parse_obj(&mut blocks[0])
        .expect("parse object line")
}

fn assert_negation(obj: &Obj) -> &Obj {
    let Obj::Mul(negation) = obj else {
        panic!("expected prefix minus to lower to multiplication, got {obj}");
    };
    assert_eq!(negation.left.to_string(), "-1");
    negation.right.as_ref()
}

#[test]
fn power_binds_tighter_than_prefix_minus() {
    let parsed = parse_obj_line("-2^2");
    let explicit_negation = parse_obj_line("-(2^2)");
    let explicit_negative_base = parse_obj_line("(-2)^2");

    assert!(matches!(assert_negation(&parsed), Obj::Pow(_)));
    assert_eq!(parsed.to_string(), explicit_negation.to_string());
    assert_eq!(parsed.to_string(), "-1 * 2 ^ 2");
    assert_eq!(explicit_negative_base.to_string(), "(-1 * 2) ^ 2");
    assert!(matches!(explicit_negative_base, Obj::Pow(_)));
}

#[test]
fn prefix_minus_binds_tighter_than_multiplicative_and_additive_operators() {
    let product = parse_obj_line("-2 * 3");
    let quotient = parse_obj_line("-2 / 3");
    let sum = parse_obj_line("-2 + 3");

    let Obj::Mul(product) = product else {
        panic!("expected outer multiplication");
    };
    assert!(matches!(product.left.as_ref(), Obj::Mul(_)));
    assert_eq!(product.right.to_string(), "3");

    let Obj::Div(quotient) = quotient else {
        panic!("expected outer division");
    };
    assert!(matches!(quotient.left.as_ref(), Obj::Mul(_)));
    assert_eq!(quotient.right.to_string(), "3");

    let Obj::Add(sum) = sum else {
        panic!("expected outer addition");
    };
    assert!(matches!(sum.left.as_ref(), Obj::Mul(_)));
    assert_eq!(sum.right.to_string(), "3");
}

#[test]
fn powers_remain_right_associative_and_accept_negative_exponents() {
    let tower = parse_obj_line("2^3^2");
    let Obj::Pow(tower) = tower else {
        panic!("expected outer power");
    };
    assert!(matches!(tower.exponent.as_ref(), Obj::Pow(_)));

    let bare_negative_exponent = parse_obj_line("2^-3^2");
    let Obj::Pow(power) = &bare_negative_exponent else {
        panic!("expected power with a negative exponent");
    };
    assert!(matches!(
        assert_negation(power.exponent.as_ref()),
        Obj::Pow(_)
    ));

    let parenthesized_negative_exponent = parse_obj_line("2^(-(3^2))");
    assert_eq!(
        bare_negative_exponent.to_string(),
        parenthesized_negative_exponent.to_string()
    );
}

#[test]
fn postfixes_bind_tighter_than_power_and_signed_range_endpoints_still_parse() {
    let indexed_power = parse_obj_line("-x[1]^2");
    let Obj::Pow(power) = assert_negation(&indexed_power) else {
        panic!("expected negated indexed power");
    };
    assert!(matches!(power.base.as_ref(), Obj::ObjAtIndex(_)));

    let powered_negative_index = parse_obj_line("(-x)[1]^2");
    let Obj::Pow(power) = powered_negative_index else {
        panic!("expected powered indexed negative value");
    };
    let Obj::ObjAtIndex(indexed) = power.base.as_ref() else {
        panic!("expected indexed power base");
    };
    assert!(matches!(indexed.obj.as_ref(), Obj::Mul(_)));

    let range = parse_obj_line("-1...1");
    let Obj::ClosedRange(range) = range else {
        panic!("expected a closed range");
    };
    assert!(matches!(range.start.as_ref(), Obj::Mul(_)));
    assert_eq!(range.end.to_string(), "1");
}
