//! Result contracts for fact storage and transitive closure inference.

use crate::output::render_statement_result_json;
use crate::prelude::*;
use crate::test_support::execute_source;

#[test]
fn registered_transitive_predicate_chain_store_returns_typed_closure_inference() {
    let mut runtime = Runtime::default();
    runtime.start_isolated_source("registered_transitive_predicate_chain_result_test.lit");
    let (_, setup_error) = execute_source(
        "prop same_set(x set, y set):\n    x = y\ntrust R $same_set C\ntrust C $same_set N",
        &mut runtime,
    );
    assert!(setup_error.is_none(), "{setup_error:?}");
    runtime
        .top_level_env()
        .store_transitive_prop_name("same_set".to_string());

    let (mut results, error) = execute_source("R $same_set C $same_set N", &mut runtime);
    assert!(error.is_none(), "{error:?}");
    let result = results.pop().expect("chain execution returns one Result");
    let success = result
        .factual_success()
        .expect("registered transitive chain should succeed");
    let application = success
        .store
        .infers
        .rule_applications
        .iter()
        .find(|application| {
            matches!(
                application.rule,
                InferRule::RegisteredTransitivePredicateChainClosure(_)
            )
        })
        .expect("three-object chain should retain one typed transitive application");
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
    let InferRule::RegisteredTransitivePredicateChainClosure(rule) = &application.rule else {
        panic!("chain closure should retain its typed transitive rule")
    };
    assert_eq!(rule.predicate_name, "same_set");
    assert_eq!(rule.start_object_index, 0);
    assert_eq!(rule.end_object_index, 2);
    assert_eq!(
        application
            .premises
            .iter()
            .map(|premise| premise.fact.to_string())
            .collect::<Vec<_>>(),
        vec!["$same_set(R, C)", "$same_set(C, N)"]
    );
    assert!(
        application
            .premises
            .iter()
            .all(|premise| premise.fact_id.is_some()),
        "every transitive premise must freeze its exact FactId"
    );
    let [conclusion] = application.conclusions.as_slice() else {
        panic!("transitive application should retain exactly one stored conclusion")
    };
    assert_eq!(conclusion.fact.to_string(), "$same_set(R, N)");
    assert!(conclusion.fact_id.is_some());
    assert!(success
        .store
        .infers
        .store_fact_outputs
        .iter()
        .any(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    fact.to_string() == conclusion.fact.to_string()
                        && *fact_id == conclusion.fact_id
                })
        }));
    let json = render_statement_result_json(&result);
    assert!(json.contains("\"rule\": \"RegisteredTransitivePredicateChainClosure\""));
    assert!(json.contains("\"predicate_name\": \"same_set\""));
    assert!(json.contains("\"start_object_index\": 0"));
    assert!(json.contains("\"end_object_index\": 2"));
}
