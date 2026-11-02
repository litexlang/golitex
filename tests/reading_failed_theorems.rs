//! Rejected theorem applications retain ordered checks without publishing goals.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

trait Field {
    fn field(&self, name: &str) -> &JsonValue;
}
impl Field for JsonValue {
    fn field(&self, name: &str) -> &JsonValue {
        self.as_object()
            .ok()
            .and_then(|o| o.get(name))
            .unwrap_or(&JsonValue::Null)
    }
}
fn resolve(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = value.clone();
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        value = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|r| r.field("id") == value.field("evidence_id"))
            .unwrap()
            .field("node")
            .clone();
    }
    value
}
fn unwrap(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = resolve(document, value);
    while value.field("fields").field("0") != &JsonValue::Null {
        value = resolve(document, value.field("fields").field("0"));
    }
    value
}
fn nodes(document: &JsonValue, name: &str) -> Vec<JsonValue> {
    document
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r.field("node"))
        .filter(|n| n.field("type").as_str().ok() == Some(name))
        .cloned()
        .collect()
}
fn rejected(source: &str) -> JsonValue {
    let built = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!built.success, "{source}");
    for s in built.document.field("statements").as_array().unwrap() {
        if s.field("status").as_str().ok() == Some("rejected") {
            assert!(s.field("produced_fact_ids").as_array().unwrap().is_empty());
        }
    }
    built.document
}
fn paired_checks(
    document: &JsonValue,
    checks: &JsonValue,
    requirements: &[JsonValue],
    count: usize,
) {
    let checks = checks.as_array().unwrap();
    assert_eq!(checks.len(), count);
    for (i, check) in checks.iter().enumerate() {
        let fields = resolve(document, check).field("fields").clone();
        let proof = unwrap(document, fields.field("proof"));
        assert!(proof.field("type").as_str().unwrap().ends_with("Success"));
        assert_eq!(
            unwrap(document, proof.field("fields").field("fact")),
            unwrap(document, &requirements[i])
        );
        let store = resolve(document, fields.field("stored"));
        assert_eq!(
            store.field("type").as_str().unwrap(),
            "StoreFactAndInferResult"
        );
    }
}

#[test]
fn later_failed_premise_retains_actual_argument_and_premise_prefixes() {
    let d = rejected("thm sum_positive:\n    ? forall x,y,z R:\n        x>0\n        y>0\n        z>0\n        =>:\n            x+y+z>0\nrelease thm sum_positive(1,0,1)\n");
    let contexts = nodes(&d, "TheoremInvocationLocalFailure");
    assert_eq!(contexts.len(), 1);
    let c = contexts[0].field("fields");
    let prepared = resolve(&d, c.field("prepared"));
    let p = prepared.field("fields");
    let failed = unwrap(&d, c.field("failure"));
    assert_eq!(
        failed.field("type").as_str().unwrap(),
        "TheoremInvocationFailed"
    );
    assert_eq!(failed.field("variant").as_str().unwrap(), "Premise");
    let f = failed.field("fields");
    paired_checks(
        &d,
        f.field("type_checks"),
        p.field("type_facts").as_array().unwrap(),
        3,
    );
    paired_checks(
        &d,
        f.field("premise_checks"),
        p.field("dom_facts").as_array().unwrap(),
        1,
    );
    let cause = unwrap(&d, f.field("failure"));
    assert_eq!(cause.field("variant").as_str().unwrap(), "Dom");
    assert_eq!(cause.field("fields").field("index").as_str().unwrap(), "1");
    assert_eq!(
        unwrap(&d, cause.field("fields").field("fact")),
        unwrap(&d, &p.field("dom_facts").as_array().unwrap()[1])
    );
    let local = resolve(&d, c.field("local_env"));
    let statement = d
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("status").as_str().ok() == Some("rejected"))
        .unwrap();
    let scope = d
        .field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("id") == local.field("scope_id"))
        .unwrap();
    assert_eq!(scope.field("statement_id"), statement.field("id"));
    assert_eq!(scope.field("parent_id"), statement.field("scope_id"));
}

#[test]
fn dependent_argument_failure_retains_only_the_preceding_argument_check() {
    let d = rejected("thm reflexive:\n    ? forall A nonempty_set,x A:\n        x=x\nby thm reflexive({1},2) => 2=2\n");
    let failed = nodes(&d, "TheoremInvocationFailed");
    assert_eq!(failed[0].field("variant").as_str().unwrap(), "Type");
    assert_eq!(
        failed[0]
            .field("fields")
            .field("type_checks")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(failed[0]
        .field("fields")
        .field("premise_checks")
        .as_array()
        .is_err());
}

#[test]
fn tuple_right_domain_failure_keeps_the_successful_left_peer() {
    let d = rejected("release thm tuple_equal_from_coordinates((1,2),(1,2,3))\n");
    let failures = nodes(&d, "TheoremFunctionDomainFailure");
    assert_eq!(failures.len(), 1);
    assert_eq!(
        failures[0]
            .field("fields")
            .field("completed_peers")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let d = rejected("have fn short_tuple(k closed_range(1,2)) R=k\nrelease thm tuple_equal_from_coordinates(short_tuple,(1,2,3))\n");
    assert!(nodes(&d, "TheoremFunctionDomainFailure")[0]
        .field("fields")
        .field("completed_peers")
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn selection_failure_retains_local_returns_and_preparation_does_not_enter_scope() {
    let d = rejected("thm reflexive:\n    ? forall A nonempty_set,x A:\n        x=x\nby thm reflexive({1},1) => 2=2\n");
    let failures = nodes(&d, "TheoremInvocationLocalFailed");
    assert_eq!(failures[0].field("variant").as_str().unwrap(), "Selection");
    assert_eq!(
        failures[0]
            .field("fields")
            .field("returned_conclusions")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(nodes(&d, "VerifiedTheoremInvocation").len(), 1);
    let d = rejected("release thm missing_theorem(1)\n");
    assert_eq!(nodes(&d, "TheoremInvocationPreparationFailure").len(), 1);
    assert!(nodes(&d, "TheoremInvocationLocalFailure").is_empty());
}
