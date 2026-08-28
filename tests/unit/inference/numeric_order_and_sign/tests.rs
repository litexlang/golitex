use crate::prelude::*;
use crate::test_support::execute_source;
use crate::verification::{compare_normalized_number_str_to_zero, NumberCompareResult};

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

#[test]
fn positive_literal_bound_retains_typed_zero_sign_inference() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("numeric_order_bound_result_test.lit");
    let (mut results, error) = execute_source("have n Z\ntrust n >= 1", &mut runtime);
    assert!(error.is_none(), "{error:?}");
    let result = results.pop().expect("trust statement returns one Result");
    let StmtResult::Success(success) = result else {
        panic!("trusted numeric bound should succeed")
    };
    let common = success.common().expect("trust statement has common Result");
    let [application] = common.infers.rule_applications.as_slice() else {
        panic!("numeric bound should retain one typed sign inference")
    };
    assert!(matches!(
        application.rule,
        InferRule::NumericOrderBoundImpliesZeroSign
    ));
    let [premise] = application.premises.as_slice() else {
        panic!("numeric sign inference should cite one source bound")
    };
    assert!(premise.fact.to_string().ends_with("n >= 1"));
    assert!(premise.fact_id.is_some());
    let [conclusion] = application.conclusions.as_slice() else {
        panic!("numeric sign inference should retain one conclusion")
    };
    assert!(conclusion.fact.to_string().ends_with("n"));
    assert!(conclusion.fact.to_string().starts_with("0 < "));
    assert!(conclusion.fact_id.is_some());
}
