//! Result contracts for equality-chain closure inference.

use crate::output::render_statement_result_json;
use crate::prelude::*;
use crate::test_support::execute_source;

#[test]
fn equality_chain_store_returns_typed_exact_interval_closure() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("equality_chain_result_test.lit");

    let (mut results, error) = execute_source("1+0=1=0+1", &mut runtime);
    assert!(error.is_none(), "{error:?}");
    let result = results.pop().expect("chain execution returns one Result");
    let success = result
        .factual_success()
        .expect("verified equality chain should be stored");
    let application = success
        .store
        .infers
        .rule_applications
        .iter()
        .find(|application| matches!(application.rule, InferRule::EqualityChainClosure(_)))
        .expect("three-object equality chain should retain one typed closure application");
    assert_eq!(
        success
            .store
            .infers
            .rule_applications
            .iter()
            .filter(|application| matches!(application.rule, InferRule::ChainImpliesComponent(_)))
            .count(),
        2,
        "the source chain should also retain its two ordered component projections"
    );
    let InferRule::EqualityChainClosure(rule) = &application.rule else {
        panic!("equality closure should retain its typed rule")
    };
    assert_eq!(rule.start_object_index, 0);
    assert_eq!(rule.end_object_index, 2);
    assert_eq!(
        application
            .premises
            .iter()
            .map(|premise| premise.fact.to_string())
            .collect::<Vec<_>>(),
        vec!["1 + 0 = 1", "1 = 0 + 1"]
    );
    assert!(application
        .premises
        .iter()
        .all(|premise| premise.fact_id.is_some()));
    let [conclusion] = application.conclusions.as_slice() else {
        panic!("equality closure should retain one stored conclusion")
    };
    assert_eq!(conclusion.fact.to_string(), "1 + 0 = 0 + 1");
    assert!(conclusion.fact_id.is_some());
    assert!(success
        .store
        .infers
        .store_fact_outputs
        .iter()
        .any(|output| output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
            .any(|(fact, fact_id)| fact.to_string() == "1 + 0 = 0 + 1"
                && *fact_id == conclusion.fact_id)));

    let json = render_statement_result_json(&result);
    assert!(json.contains("\"rule\": \"EqualityChainClosure\""));
    assert!(json.contains("\"start_object_index\": 0"));
    assert!(json.contains("\"end_object_index\": 2"));
}
