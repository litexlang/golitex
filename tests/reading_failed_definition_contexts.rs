//! Actual enclosing definition failures, ordered WD assumptions and detached scopes.
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

fn scope_owner(document: &JsonValue, reference: &JsonValue, parent: &JsonValue) -> JsonValue {
    let env = resolve(document, reference);
    let id = env.field("scope_id");
    let source = document
        .field("statements")
        .as_array()
        .unwrap()
        .first()
        .unwrap();
    let scope = document
        .field("scopes")
        .as_array()
        .unwrap()
        .iter()
        .find(|scope| scope.field("id") == id)
        .unwrap();
    assert_eq!(scope.field("statement_id"), source.field("id"));
    assert_eq!(scope.field("parent_id"), parent);
    id.clone()
}

#[test]
fn all_three_parameter_failures_keep_the_actual_first_group_and_local_scope() {
    for (source, owner) in [
        (
            "prop P(a R, b {1 / 0}):\n    a = a",
            "ExecDefPropLocalFailure",
        ),
        (
            "struct BadHeader<A set, b {1 / 0}>:\n    x A\n    y A",
            "ExecDefStructLocalFailure",
        ),
        (
            "template<A set, b {1 / 0}>:\n    have bad_parameter_body set = A",
            "ExecDefTemplateLocalFailure",
        ),
    ] {
        let d = build(source, false);
        let owners = nodes(&d, owner);
        assert_eq!(owners.len(), 1);
        let fields = owners[0].field("fields");
        scope_owner(
            &d,
            fields.field("local_env"),
            &JsonValue::String("file:source0".into()),
        );
        let stage = resolve(&d, fields.field("failure"));
        assert_eq!(stage.field("variant").as_str().unwrap(), "Parameters");
        let prefix = resolve(&d, stage.field("fields").field("0"));
        assert_eq!(
            prefix.field("variant").as_str().unwrap(),
            "ParamTypeWithPrefix"
        );
        assert_eq!(
            prefix
                .field("fields")
                .field("param_type_well_defined")
                .as_array()
                .unwrap()
                .len(),
            1
        );
        let stored = resolve(&d, prefix.field("fields").field("defined_params"));
        assert_eq!(
            stored
                .field("fields")
                .field("stored_fact_ids")
                .as_array()
                .unwrap()
                .len(),
            1
        );
    }
}

#[test]
fn predicate_failure_retains_a_local_condition_assumption_without_proving_an_instance() {
    let d = build(
        "prop guarded(x R):\n    x > 0\n    1 / (x - 1) $in R\n    x = x",
        false,
    );
    let owners = nodes(&d, "ExecDefPropLocalFailure");
    let fields = owners[0].field("fields");
    let scope = scope_owner(
        &d,
        fields.field("local_env"),
        &JsonValue::String("file:source0".into()),
    );
    let stage = resolve(&d, fields.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "Condition");
    let assumptions = stage
        .field("fields")
        .field("assumed_iff_facts")
        .as_array()
        .unwrap();
    assert_eq!(assumptions.len(), 1);
    assert_eq!(
        resolve(&d, &assumptions[0]).field("type").as_str().unwrap(),
        "AssumeDomFactResult"
    );
    let temporary = d
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f.field("text").as_str().ok() == Some("x > 0"))
        .unwrap();
    assert_eq!(temporary.field("scope_id"), &scope);
    assert!(nodes(&d, "ExecDefPropStmtSuccessResult").is_empty());
}

#[test]
fn structure_field_failure_keeps_nested_scope_and_only_the_completed_field() {
    let d = build("struct BadFields:\n    x R\n    y {1 / 0}", false);
    let owners = nodes(&d, "ExecDefStructLocalFailure");
    let fields = owners[0].field("fields");
    let outer = scope_owner(
        &d,
        fields.field("local_env"),
        &JsonValue::String("file:source0".into()),
    );
    let stage = resolve(&d, fields.field("failure"));
    let inner = resolve(&d, stage.field("fields").field("field_failure"));
    scope_owner(&d, inner.field("fields").field("field_local_env"), &outer);
    let failure = resolve(&d, inner.field("fields").field("failure"));
    assert_eq!(failure.field("variant").as_str().unwrap(), "Field");
    assert_eq!(
        failure
            .field("fields")
            .field("fields")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(nodes(&d, "ExecDefStructStmtSuccessResult").is_empty());
}

#[test]
fn structure_condition_failure_keeps_both_fields_and_the_actual_condition_prefix() {
    let d = build("struct BadLaw:\n    x R\n    y R\n    <=>:\n        x > 0\n        1 / (x - 1) $in R\n        y = y", false);
    let stages = nodes(&d, "DefStructFieldLocalFailed");
    let stage = &stages[0];
    assert_eq!(stage.field("variant").as_str().unwrap(), "Condition");
    assert_eq!(
        stage
            .field("fields")
            .field("fields")
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        stage
            .field("fields")
            .field("equivalent_facts")
            .as_array()
            .unwrap()
            .len(),
        1
    );
}

#[test]
fn template_domain_failure_does_not_execute_its_body() {
    let d = build(
        "template<x R: $is_set({x}), $is_set({1 / (x - 1)})>:\n    have bad_domain_body R = x",
        false,
    );
    let owners = nodes(&d, "ExecDefTemplateLocalFailure");
    let fields = owners[0].field("fields");
    scope_owner(
        &d,
        fields.field("local_env"),
        &JsonValue::String("file:source0".into()),
    );
    let stage = resolve(&d, fields.field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "Domain");
    assert_eq!(
        stage
            .field("fields")
            .field("assumed_dom_facts")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert!(nodes(&d, "ExecHaveObjEqualAfterPreflightFailure").is_empty());
}

#[test]
fn template_body_failure_retains_parameter_context_and_the_actual_child_failure() {
    let d = build("template<T set>:\n    have bad_value R = 1 / 0", false);
    let stages = nodes(&d, "DefTemplateLocalFailed");
    assert_eq!(stages[0].field("variant").as_str().unwrap(), "Body");
    assert_ne!(
        stages[0].field("fields").field("introduced_params"),
        &JsonValue::Null
    );
    assert_eq!(nodes(&d, "ExecHaveObjEqualAfterPreflightFailure").len(), 1);
}

#[test]
fn successful_definition_records_do_not_gain_failure_wrappers() {
    for source in [
        "prop guarded(x R):\n    x > 0\n    x != 1\n    1 / (x - 1) $in R\n    x = x",
        "struct GoodFields:\n    x R\n    y R",
        "template<T set>:\n    have good_value R = 1 / 2",
    ] {
        let d = build(source, true);
        for owner in [
            "ExecDefPropLocalFailure",
            "ExecDefStructLocalFailure",
            "ExecDefTemplateLocalFailure",
        ] {
            assert!(nodes(&d, owner).is_empty());
        }
    }
}
