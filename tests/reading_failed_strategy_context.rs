//! Actual strategy body executions retain source, citation and local identities.
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
            .and_then(|fields| fields.get(name))
            .unwrap_or(&JsonValue::Null)
    }
}
fn resolve(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut node = value.clone();
    while node.field("kind").as_str().ok() == Some("evidence_reference") {
        node = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == node.field("evidence_id"))
            .unwrap()
            .field("node")
            .clone();
    }
    node
}
fn result(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut node = resolve(document, value);
    while node
        .field("fields")
        .as_object()
        .ok()
        .is_some_and(|fields| fields.get("0").is_some())
    {
        node = resolve(document, node.field("fields").field("0"));
    }
    node
}
fn statement(document: &JsonValue, id: &JsonValue) -> JsonValue {
    document
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|value| value.field("id") == id)
        .unwrap()
        .clone()
}
fn strategy(document: &JsonValue) -> JsonValue {
    document
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|value| {
            value.field("statement_kind").as_str().ok() == Some("Definition.DefStrategyStmt")
        })
        .unwrap()
        .clone()
}
fn build(source: &str, success: bool) -> JsonValue {
    let output = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert_eq!(output.success, success, "{source}");
    output.document
}
const SOURCE: &str = include_str!(
    "../examples/test_statements/negative/def_strategy_stmt/retained-final-prefix.lit"
);

#[test]
fn failed_strategy_retains_local_scope_and_only_actual_source_steps() {
    let document = build(SOURCE, false);
    let owner = strategy(&document);
    assert_eq!(owner.field("status").as_str().unwrap(), "rejected");
    assert!(owner
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    assert!(owner
        .field("inferred_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    let local = result(&document, owner.field("evidence"));
    assert_eq!(
        local.field("type").as_str().unwrap(),
        "ExecDefStrategyLocalFailure"
    );
    let fields = local.field("fields");
    let scope = resolve(&document, fields.field("local_env"));
    let entered = resolve(&document, fields.field("body"));
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
    let failed = resolve(&document, entered.field("fields").field("failure"));
    assert_eq!(failed.field("variant").as_str().unwrap(), "Conclusion");
    let stages = failed.field("fields");
    assert_eq!(stages.field("index").as_str().unwrap(), "1");
    assert_eq!(
        stages.field("conclusion_proofs").as_array().unwrap().len(),
        1
    );
    let steps = stages.field("proof_steps").as_array().unwrap();
    assert_eq!(steps.len(), 2);
    for reference in steps {
        assert_eq!(
            reference.field("kind").as_str().unwrap(),
            "statement_reference"
        );
        let child = statement(&document, reference.field("statement_id"));
        assert_eq!(child.field("status").as_str().unwrap(), "accepted");
        assert_eq!(child.field("parent_statement_id"), owner.field("id"));
        assert_eq!(child.field("scope_id"), scope.field("scope_id"));
        for id in child.field("produced_fact_ids").as_array().unwrap() {
            let fact = document
                .field("facts")
                .as_array()
                .unwrap()
                .iter()
                .find(|fact| fact.field("id") == id)
                .unwrap();
            assert_eq!(fact.field("scope_id"), scope.field("scope_id"));
            assert_eq!(fact.field("producer_statement_id"), child.field("id"));
        }
    }
}

#[test]
fn later_outer_declaration_has_distinct_binding_after_failed_strategy() {
    let document = build(&format!("{SOURCE}\nhave helper R = 1\nhelper = 1\n"), false);
    let rows = document.field("statements").as_array().unwrap();
    let helpers: Vec<_> = rows
        .iter()
        .filter(|s| {
            s.field("statement_kind").as_str().ok() == Some("Definition.DefineObj.HaveObjEqualStmt")
        })
        .collect();
    assert_eq!(helpers.len(), 2);
    assert_ne!(helpers[0].field("scope_id"), helpers[1].field("scope_id"));
    assert_ne!(
        helpers[0].field("declaration_symbol_ids"),
        helpers[1].field("declaration_symbol_ids")
    );
    assert_eq!(
        rows.last().unwrap().field("status").as_str().unwrap(),
        "accepted"
    );
}

#[test]
fn inference_occurrences_follow_their_own_stored_conclusion_scopes() {
    let document = build(
        include_str!(
            "../examples/test_statements/negative/def_strategy_stmt/retained-inference-scopes.lit"
        ),
        false,
    );
    let local = result(&document, strategy(&document).field("evidence"));
    let body_scope = resolve(&document, local.field("fields").field("local_env"));
    let entered = resolve(&document, local.field("fields").field("body"));
    let assumption = resolve(
        &document,
        &entered
            .field("fields")
            .field("assumed_dom_facts")
            .as_array()
            .unwrap()[0],
    );
    let stored = resolve(
        &document,
        assumption.field("fields").field("store_and_infer"),
    );
    let actual_infer = stored.field("fields").field("infer");
    let batches = document.field("inferences").as_array().unwrap();
    assert_eq!(batches.len(), 2);
    assert_eq!(
        batches[0].field("source_fact_id"),
        batches[1].field("source_fact_id")
    );
    assert_ne!(batches[0].field("scope_id"), batches[1].field("scope_id"));
    for batch in batches {
        for id in batch.field("fact_ids").as_array().unwrap() {
            let fact = document
                .field("facts")
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row.field("id") == id)
                .unwrap();
            assert_eq!(batch.field("scope_id"), fact.field("scope_id"));
        }
        if batch.field("evidence") == actual_infer {
            assert_eq!(batch.field("scope_id"), body_scope.field("scope_id"));
        } else {
            assert_ne!(batch.field("scope_id"), body_scope.field("scope_id"));
        }
    }
}

#[test]
fn published_definition_consequences_keep_their_outer_publication_scope() {
    let document = build(
        include_str!("../examples/reading/lessons/en/definitions.lit"),
        true,
    );
    for batch in document.field("inferences").as_array().unwrap() {
        for id in batch.field("fact_ids").as_array().unwrap() {
            let fact = document
                .field("facts")
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row.field("id") == id)
                .unwrap();
            assert_eq!(batch.field("scope_id"), fact.field("scope_id"));
        }
    }
    assert!(document
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .any(|row| row.field("scope_id").as_str().ok() == Some("file:source0")));
}
