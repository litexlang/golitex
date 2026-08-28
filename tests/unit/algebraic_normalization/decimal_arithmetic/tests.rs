use super::*;

#[test]
fn evaluation_result_retains_the_recursive_addition_tree() {
    let expression: Obj = Add::new(
        Number::new("2".to_string()).into(),
        Number::new("3".to_string()).into(),
    )
    .into();

    let result = expression
        .evaluate_to_normalized_decimal_number_with_result()
        .expect("2 + 3 should decimal_arithmetic");

    assert_eq!(result.expression.to_string(), "2 + 3");
    assert_eq!(result.value.normalized_value, "5");
    let SuccessEvaluateObjStepResult::Binary(binary) = result.step else {
        panic!("2 + 3 should retain a binary evaluation step");
    };
    assert_eq!(binary.operator, EvaluateBinaryObjOperator::Add);
    assert_eq!(binary.left.expression.to_string(), "2");
    assert_eq!(binary.left.value.normalized_value, "2");
    assert!(matches!(
        binary.left.step,
        SuccessEvaluateObjStepResult::Literal(_)
    ));
    assert_eq!(binary.right.expression.to_string(), "3");
    assert_eq!(binary.right.value.normalized_value, "3");
    assert!(matches!(
        binary.right.step,
        SuccessEvaluateObjStepResult::Literal(_)
    ));
}

#[test]
fn huge_power_is_left_unevaluated() {
    assert_eq!(pow_decimal_str_and_normalize("5", "999999"), None);
}

#[test]
fn mod_of_huge_power_is_left_unevaluated() {
    let base: Obj = Number::new("5".to_string()).into();
    let exponent: Obj = Number::new("999999".to_string()).into();
    let modulus: Obj = Number::new("7".to_string()).into();
    let power: Obj = Pow::new(base, exponent).into();
    let remainder: Obj = Mod::new(power, modulus).into();

    assert!(remainder.evaluate_to_normalized_decimal_number().is_none());
}

#[test]
fn power_above_one_hundred_digits_is_left_unevaluated() {
    let base: Obj = Number::new("5".to_string()).into();
    let exponent: Obj = Number::new("2005".to_string()).into();
    let modulus: Obj = Number::new("100".to_string()).into();
    let power: Obj = Pow::new(base, exponent).into();
    let remainder: Obj = Mod::new(power, modulus).into();

    assert!(remainder.evaluate_to_normalized_decimal_number().is_none());
}

#[test]
fn bounded_power_mod_still_evaluates() {
    let base: Obj = Number::new("5".to_string()).into();
    let exponent: Obj = Number::new("30".to_string()).into();
    let modulus: Obj = Number::new("7".to_string()).into();
    let power: Obj = Pow::new(base, exponent).into();
    let remainder: Obj = Mod::new(power, modulus).into();

    let result = remainder
        .evaluate_to_normalized_decimal_number()
        .map(|number| number.normalized_value);
    assert_eq!(result, Some("1".to_string()));
}

#[test]
fn signed_mod_uses_euclidean_remainders() {
    assert_eq!(mod_decimal_str_and_normalize("7", "3"), "1");
    assert_eq!(mod_decimal_str_and_normalize("-7", "3"), "2");
    assert_eq!(mod_decimal_str_and_normalize("-6", "3"), "0");
    assert_eq!(mod_decimal_str_and_normalize("-7", "-3"), "2");
}

#[test]
fn signed_quot_uses_euclidean_quotients() {
    assert_eq!(quot_decimal_str_and_normalize("7", "3"), "2");
    assert_eq!(quot_decimal_str_and_normalize("-7", "3"), "-3");
    assert_eq!(quot_decimal_str_and_normalize("-6", "3"), "-2");
    assert_eq!(
        quot_decimal_str_and_normalize("1234567890123456789012345678900", "10"),
        "123456789012345678901234567890"
    );
}
