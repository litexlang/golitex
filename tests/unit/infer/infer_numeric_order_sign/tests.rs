use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

#[test]
fn compare_to_zero_matches_expectations() {
    assert!(matches!(
        compare_normalized_number_str_to_zero("1"),
        NumberCompareResult::Greater
    ));
    assert!(matches!(
        compare_normalized_number_str_to_zero("0"),
        NumberCompareResult::Equal
    ));
    assert!(matches!(
        compare_normalized_number_str_to_zero("-2"),
        NumberCompareResult::Less
    ));
}
