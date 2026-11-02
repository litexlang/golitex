//! Failed claims retain checked stage prefixes in detached native scopes.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

trait Field {
    fn field(&self, key: &str) -> &JsonValue;
}
impl Field for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .ok()
            .and_then(|fields| fields.get(key))
            .unwrap_or(&JsonValue::Null)
    }
}
fn document(source: &str) -> JsonValue {
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    result.document
}
fn resolve(data: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = value.clone();
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        value = data
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == value.field("evidence_id"))
            .unwrap()
            .field("node")
            .clone();
    }
    value
}
fn nodes(data: &JsonValue, name: &str) -> Vec<JsonValue> {
    data.field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.field("node"))
        .filter(|node| node.field("type").as_str().ok() == Some(name))
        .cloned()
        .collect()
}
fn statement(data: &JsonValue, number: u64) -> JsonValue {
    data.field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("line").as_u64().ok() == Some(number))
        .unwrap()
        .clone()
}
fn context_scope(data: &JsonValue, context: &JsonValue) -> JsonValue {
    let scope = resolve(data, context.field("fields").field("local_env"));
    let id = scope.field("scope_id");
    assert!(!id.as_str().unwrap().starts_with("file:"));
    data.field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("id") == id)
        .unwrap()
        .clone()
}

#[test]
fn failed_quantified_body_keeps_parameters_premise_and_exact_checked_prefix() {
    let data = document("claim:\n    ? forall x R:\n        x > 0\n        =>:\n            x >= 0\n    x > 0\n    2 = 3\n    x >= 0\n");
    let contexts = nodes(&data, "ExecClaimLocalFailure");
    assert_eq!(contexts.len(), 1);
    let scope = context_scope(&data, &contexts[0]);
    assert_eq!(scope.field("statement_id"), statement(&data, 1).field("id"));
    let body = resolve(&data, contexts[0].field("fields").field("body"));
    let entered = resolve(&data, body.field("fields").field("0"));
    assert_eq!(entered.field("variant").as_str().unwrap(), "Entered");
    assert_eq!(
        entered
            .field("fields")
            .field("assumed_dom_facts")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        resolve(&data, entered.field("fields").field("introduced_params"))
            .field("type")
            .as_str()
            .unwrap(),
        "IntroduceTypedParametersResult"
    );
    for (line, status) in [
        (1, "rejected"),
        (6, "accepted"),
        (7, "rejected"),
        (8, "not_exported"),
    ] {
        assert_eq!(
            statement(&data, line).field("status").as_str().unwrap(),
            status
        );
    }
    assert!(statement(&data, 1)
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    assert!(data
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .any(|f| f.field("text").as_str().ok() == Some("x $in R")
            && f.field("scope_id") == scope.field("id")));
}

#[test]
fn failed_closing_goal_retains_prior_body_and_prior_conclusion_checks() {
    let data = document("claim:\n    ? forall t R:\n        t = t\n        t >= 0\n    t = t\n");
    let failed = nodes(&data, "ExecClaimForallEnteredFailed").remove(0);
    assert_eq!(failed.field("variant").as_str().unwrap(), "Conclusion");
    assert_eq!(
        failed
            .field("fields")
            .field("index")
            .as_str()
            .unwrap()
            .parse::<usize>()
            .unwrap(),
        1
    );
    assert_eq!(
        failed
            .field("fields")
            .field("proof_steps")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        failed
            .field("fields")
            .field("conclusion_proofs")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(
        statement(&data, 5).field("status").as_str().unwrap(),
        "accepted"
    );
    assert!(statement(&data, 1)
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn nonquantified_failure_retains_local_helper_and_checked_steps() {
    let data = document(
        "claim:\n    ? 1 = 1\n    have inner R = 2\n    inner = 2\n    2 = 3\n    4 = 4\n",
    );
    let scope = context_scope(&data, &nodes(&data, "ExecClaimLocalFailure")[0]);
    for (line, status) in [
        (3, "accepted"),
        (4, "accepted"),
        (5, "rejected"),
        (6, "not_exported"),
    ] {
        assert_eq!(
            statement(&data, line).field("status").as_str().unwrap(),
            status
        );
    }
    assert!(data.field("facts").as_array().unwrap().iter().any(|f| f
        .field("text")
        .as_str()
        .unwrap_or("")
        .starts_with("inner")
        && f.field("scope_id") == scope.field("id")));
}

#[test]
fn nested_failed_claims_keep_distinct_scopes_and_native_parentage() {
    let data = document("claim:\n    ? forall x R:\n        x > 0\n        =>:\n            x >= 0\n    claim:\n        ? forall y R:\n            y < 0\n            =>:\n                y <= 0\n        x > 0\n        y < 0\n        2 = 3\n    x >= 0\n");
    let contexts = nodes(&data, "ExecClaimLocalFailure");
    assert_eq!(contexts.len(), 2);
    let scopes: Vec<_> = contexts.iter().map(|c| context_scope(&data, c)).collect();
    let outer = scopes
        .iter()
        .find(|s| s.field("statement_id") == statement(&data, 1).field("id"))
        .unwrap();
    let inner = scopes
        .iter()
        .find(|s| s.field("statement_id") == statement(&data, 6).field("id"))
        .unwrap();
    assert_ne!(outer.field("id"), inner.field("id"));
    assert_eq!(inner.field("parent_id"), outer.field("id"));
    assert_eq!(
        statement(&data, 14).field("status").as_str().unwrap(),
        "not_exported"
    );
}

#[test]
fn goal_formation_failure_does_not_invent_entered_claim_context() {
    let data = document("claim:\n    ? 1 / 0 = 0\n    1 = 1\n");
    assert!(nodes(&data, "ExecClaimLocalFailure").is_empty());
    assert_eq!(
        statement(&data, 3).field("status").as_str().unwrap(),
        "not_exported"
    );
}

#[test]
fn failed_claim_premise_inferences_remain_in_its_actual_local_scope() {
    let data = document("prop positive(x R):\n    x > 0\nclaim:\n    ? forall v R:\n        $positive(v)\n        =>:\n            v >= 0\n    v > 0\n    2 = 3\n");
    let scope = context_scope(&data, &nodes(&data, "ExecClaimLocalFailure")[0]);
    let owner = statement(&data, 3);
    let context = nodes(&data, "ExecClaimLocalFailure").remove(0);
    let route = resolve(&data, context.field("fields").field("body"));
    let entered = resolve(&data, route.field("fields").field("0"));
    let assumed = resolve(
        &data,
        &entered
            .field("fields")
            .field("assumed_dom_facts")
            .as_array()
            .unwrap()[0],
    );
    let stored = resolve(&data, assumed.field("fields").field("store_and_infer"));
    let batches: Vec<_> = data
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .filter(|b| {
            b.field("producer_statement_id") == owner.field("id")
                && b.field("evidence") == stored.field("fields").field("infer")
        })
        .collect();
    assert!(!batches.is_empty());
    for batch in batches {
        assert_eq!(batch.field("scope_id"), scope.field("id"));
        for id in batch.field("fact_ids").as_array().unwrap() {
            let fact = data
                .field("facts")
                .as_array()
                .unwrap()
                .iter()
                .find(|f| f.field("id") == id)
                .unwrap();
            assert_eq!(fact.field("scope_id"), scope.field("id"));
        }
    }
    assert!(owner
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
}
