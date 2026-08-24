use super::*;

#[test]
fn exact_rational_eval_keeps_non_terminating_division() {
    let obj: Obj = Add::new(
        Number::new("1".to_string()).into(),
        Div::new(
            Number::new("1".to_string()).into(),
            Number::new("3".to_string()).into(),
        )
        .into(),
    )
    .into();
    let rational_obj = evaluate_obj_to_exact_rational_obj_for_eval(&obj).unwrap();
    assert_eq!(rational_obj.to_string(), "4 / 3");
}

#[test]
fn exact_rational_eval_reduces_decimal_and_fraction_mix() {
    let obj: Obj = Div::new(
        Number::new("1.5".to_string()).into(),
        Number::new("3".to_string()).into(),
    )
    .into();
    let rational_obj = evaluate_obj_to_exact_rational_obj_for_eval(&obj).unwrap();
    assert_eq!(rational_obj.to_string(), "1 / 2");
}
