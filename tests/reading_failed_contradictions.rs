//! Actual failed contradiction scopes, assumptions and ordered closing checks.
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
fn build(source: &str, success: bool) -> JsonValue {
    let built = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert_eq!(built.success, success, "{source}");
    for s in built.document.field("statements").as_array().unwrap() {
        if s.field("status").as_str().ok() == Some("rejected") {
            assert!(s.field("produced_fact_ids").as_array().unwrap().is_empty());
            assert!(s.field("inferred_fact_ids").as_array().unwrap().is_empty());
        }
    }
    built.document
}

#[test]
fn failed_body_retains_the_real_reverse_assumption_local_inferences_and_prefix() {
    let d=build("prop narrow(x R):\n    x>0\n    x<1\nby contra:\n    ? not $narrow(2)\n    2>0\n    7=8\n    have unexecuted R=9\n    impossible 2<1\n",false);
    let contexts = nodes(&d, "ExecByContraLocalFailure");
    assert_eq!(contexts.len(), 1);
    let c = contexts[0].field("fields");
    let stage = resolve(&d, c.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "ProofBody");
    let assumption = resolve(&d, stage.field("fields").field("assumption"));
    let id = assumption.field("fields").field("fact_id").field("fact_id");
    let reverse = unwrap(&d, c.field("reverse_assumption"));
    assert_eq!(
        reverse.field("fields").field("fact_id").field("fact_id"),
        id
    );
    let local = resolve(&d, c.field("local_env"));
    let scope = d
        .field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("id") == local.field("scope_id"))
        .unwrap();
    let owner = d
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|s| s.field("id") == scope.field("statement_id"))
        .unwrap();
    assert_eq!(scope.field("parent_id"), owner.field("scope_id"));
    assert!(d
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .any(|f| f.field("id") == id && f.field("scope_id") == scope.field("id")));
    assert!(d
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .any(|r| r.field("source_fact_id") == id && r.field("scope_id") == scope.field("id")));
    let body = resolve(&d, stage.field("fields").field("failure"));
    assert_eq!(
        body.field("fields").field("step_index").as_str().unwrap(),
        "1"
    );
    assert_eq!(
        body.field("fields")
            .field("prior_steps")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(!d.field("statements").as_array().unwrap().iter().any(|s| s
        .field("source_text")
        .as_str()
        .ok()
        .is_some_and(|text| text.starts_with("have unexecuted"))
        && s.field("status").as_str().ok() == Some("accepted")));
}

#[test]
fn failed_opposite_keeps_the_already_proved_whole_conjunction() {
    let d = build("by contra:\n    ? 1=2\n    impossible 1=1 and 0=0\n", false);
    let closings = nodes(&d, "ByContradictionAfterImpossibleFailed");
    assert_eq!(closings.len(), 1);
    let c = closings[0].field("fields");
    let proof = unwrap(&d, c.field("impossible"));
    assert_eq!(
        proof.field("type").as_str().unwrap(),
        "VerifyAndFactSuccess"
    );
    assert_eq!(
        unwrap(&d, proof.field("fields").field("fact")),
        unwrap(&d, c.field("impossible_fact"))
    );
    let opposite = unwrap(&d, c.field("failure"));
    assert_eq!(
        opposite.field("type").as_str().unwrap(),
        "VerifyOrFactFailed"
    );
}

#[test]
fn cases_share_the_same_ordered_closing_evidence() {
    let d = build(
        "by cases:\n    ? 1=2\n    case 1=1:\n        impossible 1=1\n",
        false,
    );
    assert_eq!(nodes(&d, "ByCasesBranchFailure").len(), 1);
    let c = nodes(&d, "ByContradictionAfterImpossibleFailed");
    assert_eq!(c.len(), 1);
    assert_eq!(
        unwrap(&d, c[0].field("fields").field("impossible"))
            .field("type")
            .as_str()
            .unwrap(),
        "VerifyEqualitySuccess"
    );
    assert!(nodes(&d, "ExecByContraLocalFailure").is_empty());
}

#[test]
fn closing_failure_body_steps_keep_their_executed_source_statement_identities() {
    let d = build("by contra:\n    ? 1=2\n    have temporary R=2\n    temporary=2\n    impossible 1=1 and 0=0\n", false);
    let context = nodes(&d, "ExecByContraLocalFailure");
    let fields = context[0].field("fields");
    let stage = resolve(&d, fields.field("failure"));
    let steps = stage
        .field("fields")
        .field("proof_steps")
        .as_array()
        .unwrap();
    assert_eq!(steps.len(), 2);
    let scope = resolve(&d, fields.field("local_env"));
    for reference in steps {
        assert_eq!(
            reference.field("kind").as_str().unwrap(),
            "statement_reference"
        );
        let statement = d
            .field("statements")
            .as_array()
            .unwrap()
            .iter()
            .find(|s| s.field("id") == reference.field("statement_id"))
            .unwrap();
        assert_eq!(statement.field("status").as_str().unwrap(), "accepted");
        assert_eq!(statement.field("scope_id"), scope.field("scope_id"));
        assert!(statement.field("parent_statement_id") != &JsonValue::Null);
    }
}

#[test]
fn pre_entry_failure_has_no_contradiction_assumption_and_success_contract_stays_flat() {
    for source in ["by contra:\n    ? 1/0=1\n    impossible 1=1\n","by contra:\n    ? forall y R:\n        forall z R:\n            z=z\n        =>:\n            y=y\n    impossible 1=1\n"] {
        let d=build(source,false);assert!(nodes(&d,"ExecByContraLocalFailure").is_empty());assert!(nodes(&d,"ContraAssumption").is_empty());
        if source.contains("forall y") {
            let retained = nodes(&d, "ExecByContraNegationFailure");
            assert_eq!(retained.len(), 1);
            let goal_wd = resolve(&d, retained[0].field("fields").field("goal_wd"));
            assert_eq!(goal_wd.field("variant").as_str().unwrap(), "Success");
        }
    }
    let d = build("by contra:\n    ? 1!=0\n    impossible 1=0\n", true);
    assert_eq!(nodes(&d, "ExecByContraStmtSuccess").len(), 1);
    assert!(nodes(&d, "ExecByContraLocalProof").is_empty());
}
