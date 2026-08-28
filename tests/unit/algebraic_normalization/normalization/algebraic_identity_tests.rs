use super::*;

#[test]
fn a_plus_b_squared_equals_a_minus_b_squared_plus_4ab() {
    let a = Identifier::mk("a".to_string());
    let b = Identifier::mk("b".to_string());
    let two: Obj = Number::new("2".to_string()).into();
    let four: Obj = Number::new("4".to_string()).into();

    let left = Pow::new(Add::new(a.clone(), b.clone()).into(), two.clone()).into();
    let right = Add::new(
        Pow::new(Sub::new(a.clone(), b.clone()).into(), two.clone()).into(),
        Mul::new(Mul::new(four, a.clone()).into(), b.clone()).into(),
    )
    .into();

    assert!(objs_equal_by_rational_expression_evaluation(&left, &right));
}

#[test]
fn two_an_plus_bm_squared_equals_expanded_rhs() {
    use crate::parsing::{TokenBlock, Tokenizer};
    use crate::runtime::Runtime;
    use std::rc::Rc;

    fn parse_obj_line(line: &str) -> Obj {
        let tokenizer = Tokenizer::new();
        let line_file = (1, Rc::from("test.lit"));
        let tokens = tokenizer.tokenize_line(line, line_file.clone()).unwrap();
        let mut tb = TokenBlock::new(tokens, vec![], line_file);
        let mut rt = Runtime::default();
        rt.parse_obj(&mut tb).expect("parse")
    }

    let left = parse_obj_line(r#"( 2 * a * n + b * m ) ^ 2"#);
    let right = parse_obj_line(
        r#"2 * ( a * m + b * n ) ^ 2 + ( m ^ 2 - 2 * n ^ 2 ) * ( b ^ 2 - 2 * a ^ 2 )"#,
    );
    assert!(objs_equal_by_rational_expression_evaluation(&left, &right));
}

#[test]
fn nested_divisions_reach_denominator_clearing_fixed_point() {
    let x = Identifier::mk("x".to_string());
    let one: Obj = Number::new("1".to_string()).into();
    let two: Obj = Number::new("2".to_string()).into();

    let left: Obj = Div::new(
        Sub::new(x.clone(), Div::new(x.clone(), two.clone()).into()).into(),
        x.clone(),
    )
    .into();
    let right: Obj = Sub::new(one.clone(), Div::new(one.clone(), two.clone()).into()).into();
    assert!(objs_equal_by_rational_expression_evaluation(&left, &right));

    let nested_left: Obj = Div::new(Div::new(x.clone(), two.clone()).into(), x.clone()).into();
    let nested_right: Obj = Div::new(one, two).into();
    assert!(objs_equal_by_rational_expression_evaluation(
        &nested_left,
        &nested_right
    ));
}

#[test]
fn complex_mode_reduces_imaginary_unit_products() {
    let i: Obj = ImaginaryUnit::new().into();
    let one: Obj = Number::new("1".to_string()).into();
    let two: Obj = Number::new("2".to_string()).into();

    let left: Obj = Add::new(Mul::new(two.clone(), i.clone()).into(), one.clone()).into();
    let right: Obj = Add::new(
        Add::new(Mul::new(i.clone(), i.clone()).into(), two.clone()).into(),
        Mul::new(two, i.clone()).into(),
    )
    .into();
    assert!(objs_equal_by_complex_rational_expression_evaluation(
        &left, &right
    ));

    let wrong: Obj = Number::new("1".to_string()).into();
    assert!(!objs_equal_by_complex_rational_expression_evaluation(
        &Mul::new(i.clone(), i).into(),
        &wrong,
    ));
}

#[test]
fn complex_mode_clears_imaginary_denominators() {
    let i: Obj = ImaginaryUnit::new().into();
    let one: Obj = Number::new("1".to_string()).into();
    let minus_one: Obj = Number::new("-1".to_string()).into();
    let left: Obj = Div::new(one, i.clone()).into();
    let right: Obj = Mul::new(minus_one, i).into();

    assert!(objs_equal_by_complex_rational_expression_evaluation(
        &left, &right
    ));
}
