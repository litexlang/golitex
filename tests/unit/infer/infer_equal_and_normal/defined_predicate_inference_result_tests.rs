use crate::output::display_stmt_result_json_v2;
use crate::prelude::*;

#[test]
fn defined_predicate_inference_retains_parameter_and_clause_projection_results() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("defined_predicate_inference_result_test.lit");
    let (results, error) = execute_source(
        "prop same_set(x set, y set):\n    x = y\ntrust R $same_set C",
        &mut runtime,
    );
    assert!(error.is_none(), "{error:?}");
    let [_, trust_result] = results.as_slice() else {
        panic!("expected predicate definition followed by one trust Result")
    };
    let StmtResult::Success(SuccessStmtResult::UnsafeStmt(SuccessUnsafeStmtResult::TrustStmt(
        trust,
    ))) = trust_result
    else {
        panic!("expected a successful trust Result")
    };
    let [source_output] = trust.common.infers.store_fact_outputs.as_slice() else {
        panic!("trust must retain one source store output")
    };
    let source_fact_id = source_output.fact_id.expect("source trust FactId");
    assert_eq!(trust.common.infers.rule_applications.len(), 3);
    for application in &trust.common.infers.rule_applications {
        let [premise] = application.premises.as_slice() else {
            panic!("defined-predicate projection must retain one premise")
        };
        assert_eq!(premise.fact.to_string(), "$same_set(R, C)");
        assert_eq!(premise.fact_id, Some(source_fact_id));
        let [conclusion] = application.conclusions.as_slice() else {
            panic!("defined-predicate projection must retain one conclusion")
        };
        assert!(conclusion.fact_id.is_some());
    }
    assert!(matches!(
        trust.common.infers.rule_applications[0].rule,
        InferRule::DefinedPredicateParameterRequirementProjection(
            DefinedPredicateParameterRequirementProjectionInferRule {
                parameter_index: 0,
                ..
            }
        )
    ));
    assert!(matches!(
        trust.common.infers.rule_applications[1].rule,
        InferRule::DefinedPredicateParameterRequirementProjection(
            DefinedPredicateParameterRequirementProjectionInferRule {
                parameter_index: 1,
                ..
            }
        )
    ));
    assert!(matches!(
        trust.common.infers.rule_applications[2].rule,
        InferRule::DefinedPredicateDefinitionClauseProjection(
            DefinedPredicateDefinitionClauseProjectionInferRule {
                clause_index: 0,
                ..
            }
        )
    ));
    assert_eq!(
        trust.common.infers.rule_applications[2].conclusions[0]
            .fact
            .to_string(),
        "R = C"
    );

    let json = display_stmt_result_json_v2(trust_result);
    assert!(json.contains("DefinedPredicateParameterRequirementProjection"));
    assert!(json.contains("DefinedPredicateDefinitionClauseProjection"));
    assert!(json.contains("\"predicate_name\": \"same_set\""));
    assert!(json.contains("\"parameter_index\": 0"));
    assert!(json.contains("\"clause_index\": 0"));
}
