use crate::output::display_stmt_result_json_v2;
use crate::prelude::*;

#[test]
fn conjunction_store_returns_typed_component_results_with_exact_fact_ids() {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source("conjunction_component_result_test.lit");
    let (mut results, error) = execute_source("1 = 1 and 2 = 2", &mut runtime);
    assert!(error.is_none(), "{error:?}");
    let result = results.pop().expect("one conjunction statement Result");
    let success = result
        .factual_success()
        .expect("conjunction statement should succeed");
    let source_fact_id = success
        .store
        .fact_id
        .expect("conjunction source store must retain its FactId");
    let Fact::AndFact(source_conjunction) = success.fact() else {
        panic!("source Result should retain an AndFact")
    };
    assert_eq!(source_conjunction.facts.len(), 2);
    assert_eq!(success.store.infers.rule_applications.len(), 2);

    for (component_index, application) in success.store.infers.rule_applications.iter().enumerate()
    {
        let InferRule::ConjunctionImpliesComponent(rule) = &application.rule else {
            panic!("component inference should retain its typed rule")
        };
        assert_eq!(rule.component_index, component_index);
        assert_eq!(rule.component_count, 2);
        let [premise] = application.premises.as_slice() else {
            panic!("component inference should retain one conjunction premise")
        };
        assert_eq!(premise.fact_id, Some(source_fact_id));
        let [conclusion] = application.conclusions.as_slice() else {
            panic!("component inference should retain one stored conclusion")
        };
        let component_fact_id = conclusion
            .fact_id
            .expect("component conclusion should retain its FactId");
        assert_ne!(component_fact_id, source_fact_id);
        assert_eq!(
            conclusion.fact.to_string(),
            Fact::from(source_conjunction.facts[component_index].clone()).to_string()
        );
        let [component_store] = conclusion.infers.store_fact_outputs.as_slice() else {
            panic!("component conclusion should retain its recursive store Result")
        };
        assert_eq!(component_store.fact_id, Some(component_fact_id));
    }

    let json = display_stmt_result_json_v2(&result);
    assert!(json.contains("\"rule\": \"ConjunctionImpliesComponent\""));
    assert!(json.contains("\"component_index\": 0"));
    assert!(json.contains("\"component_count\": 2"));
}
