//! Rejected theorem histories preserve actual source, scope and execution stages.
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
    while node.field("fields").field("0") != &JsonValue::Null {
        node = resolve(document, node.field("fields").field("0"));
    }
    node
}
fn build(source: &str) -> JsonValue {
    let output = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!output.success);
    output.document
}
fn theorem(document: &JsonValue) -> &JsonValue {
    document
        .field("statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row.field("statement_kind").as_str().ok() == Some("Definition.DefThmStmt"))
        .unwrap()
}
const SOURCE: &str =
    include_str!("../examples/test_statements/negative/def_thm_stmt/retained-final-prefix.lit");

#[test]
fn rejected_theorem_keeps_actual_local_prefix_without_publishing() {
    let document = build(SOURCE);
    let owner = theorem(&document);
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
        "ExecDefThmLocalFailure"
    );
    let scope = resolve(&document, local.field("fields").field("local_env"));
    let routed = resolve(&document, local.field("fields").field("body"));
    assert_eq!(routed.field("variant").as_str().unwrap(), "Forall");
    let entered = resolve(&document, routed.field("fields").field("0"));
    let stage = resolve(&document, entered.field("fields").field("failure"));
    assert_eq!(stage.field("variant").as_str().unwrap(), "Conclusion");
    assert_eq!(stage.field("fields").field("index").as_str().unwrap(), "1");
    assert_eq!(
        stage
            .field("fields")
            .field("conclusion_proofs")
            .as_array()
            .unwrap()
            .len(),
        1
    );
    let steps = stage
        .field("fields")
        .field("proof_steps")
        .as_array()
        .unwrap();
    assert_eq!(steps.len(), 2);
    let source = document.field("sources").as_array().unwrap()[0]
        .field("content")
        .as_str()
        .unwrap();
    for step in steps {
        let child = document
            .field("statements")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == step.field("statement_id"))
            .unwrap();
        assert_eq!(child.field("parent_statement_id"), owner.field("id"));
        assert_eq!(child.field("scope_id"), scope.field("scope_id"));
        assert_eq!(child.field("status").as_str().unwrap(), "accepted");
        let start = child.field("start_byte").as_u64().unwrap() as usize;
        let end = child.field("end_byte").as_u64().unwrap() as usize;
        assert_eq!(
            source[start..end].trim(),
            child.field("source_text").as_str().unwrap()
        );
    }
}

#[test]
fn nonforall_final_failure_retains_body_without_universal_introduction() {
    let document = build("prop P(x R):\n    x = 0\nthm direct_failed:\n    ? $P(1)\n    have helper R = 0\n    helper = 0\n");
    let local = result(&document, theorem(&document).field("evidence"));
    let routed = resolve(&document, local.field("fields").field("body"));
    assert_eq!(routed.field("variant").as_str().unwrap(), "NonForall");
    let failed = resolve(&document, routed.field("fields").field("0"));
    assert_eq!(
        failed.field("type").as_str().unwrap(),
        "ExecDefThmNonForallFailed"
    );
    assert_eq!(failed.field("variant").as_str().unwrap(), "Conclusion");
    assert_eq!(
        failed
            .field("fields")
            .field("proof_steps")
            .as_array()
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        failed.field("fields").field("introduced_params"),
        &JsonValue::Null
    );
}

#[test]
fn nonforall_body_failure_does_not_export_unexecuted_suffix() {
    let document = build("thm failed_body:\n    ? 1 = 1\n    have helper R = 1\n    helper = 1\n    1 = 2\n    have later R = 3\n");
    let rows = document.field("statements").as_array().unwrap();
    assert_eq!(rows[0].field("status").as_str().unwrap(), "rejected");
    let helper = rows
        .iter()
        .find(|row| row.field("source_text").as_str().ok() == Some("have helper R = 1"))
        .unwrap();
    assert_eq!(helper.field("status").as_str().unwrap(), "accepted");
    let failed = rows
        .iter()
        .find(|row| row.field("source_text").as_str().ok() == Some("1 = 2"))
        .unwrap();
    assert_eq!(failed.field("status").as_str().unwrap(), "rejected");
    let later = rows
        .iter()
        .find(|row| row.field("source_text").as_str().ok() == Some("have later R = 3"))
        .unwrap();
    assert_eq!(later.field("status").as_str().unwrap(), "not_exported");
    assert!(later
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
}

#[test]
fn outer_binding_remains_distinct_after_rejected_theorem() {
    let document = build(&format!("{SOURCE}\nhave helper R = 1\nhelper = 1\n"));
    let rows = document.field("statements").as_array().unwrap();
    let helpers: Vec<_> = rows
        .iter()
        .filter(|row| {
            row.field("statement_kind").as_str().ok()
                == Some("Definition.DefineObj.HaveObjEqualStmt")
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
