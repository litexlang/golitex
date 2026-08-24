use super::safe_div;

#[test]
fn safe_div_handles_negative_finite_decimal() {
    assert_eq!(safe_div("4", "5"), Some("0.8".to_string()));
    assert_eq!(safe_div("-4", "5"), Some("-0.8".to_string()));
    assert_eq!(safe_div("4", "-5"), Some("-0.8".to_string()));
    assert_eq!(safe_div("-4", "-5"), Some("0.8".to_string()));
}

#[test]
fn safe_div_returns_none_for_oversized_numbers() {
    assert_eq!(
        safe_div("1", "99999999999999999999999999999999999999999"),
        None
    );
    assert_eq!(
        safe_div("1", "0.000000000000000000000000000000000000001"),
        None
    );
}
