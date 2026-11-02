//! Actual strategy body executions retain source, citation and local identities.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::collections::BTreeSet;

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
const SOURCE: &str = include_str!("../examples/reading/strategy_body_steps.lit");

#[test]
fn strategy_steps_are_ordered_source_references_with_exact_utf8_ranges() {
    let source = format!("# UTF-8 source anchor: 集合\n{SOURCE}");
    let document = build(&source, true);
    let owner = strategy(&document);
    assert_eq!(owner.field("status").as_str().unwrap(), "accepted");
    assert_eq!(
        owner
            .field("coverage")
            .field("source_mapping")
            .as_str()
            .unwrap(),
        "complete"
    );
    let execution = result(&document, owner.field("evidence"));
    let body = resolve(&document, execution.field("fields").field("body"));
    let references = body
        .field("fields")
        .field("proof_steps")
        .as_array()
        .unwrap();
    let expected = [
        ("Definition.DefineObj.HaveObjEqualStmt", "have helper R = x"),
        (
            "ProofBlock.ClaimStmt",
            "claim:\n        ? helper = 0\n        helper = 0",
        ),
        (
            "Witness.WitnessExistFact",
            "witness exist u R st {u = helper} from helper",
        ),
        (
            "Definition.DefineObj.ObtainObjFromExistFact",
            "obtain u from exist u R st {u = helper}",
        ),
        ("By.ByDefStmt", "by def $same(x)"),
    ];
    assert_eq!(references.len(), expected.len());
    let mut last_line = 0;
    for (reference, (kind, authored)) in references.iter().zip(expected) {
        assert_eq!(
            reference.field("kind").as_str().unwrap(),
            "statement_reference"
        );
        let child = statement(&document, reference.field("statement_id"));
        assert_eq!(child.field("parent_statement_id"), owner.field("id"));
        assert_eq!(child.field("statement_kind").as_str().unwrap(), kind);
        assert_eq!(child.field("status").as_str().unwrap(), "accepted");
        assert_eq!(
            child.field("coverage").field("evidence").as_str().unwrap(),
            "complete"
        );
        let line = child.field("line").as_u64().unwrap();
        assert!(line > last_line);
        last_line = line;
        let start = child.field("start_byte").as_u64().unwrap() as usize;
        let end = child.field("end_byte").as_u64().unwrap() as usize;
        // source_text is a normalized rendering; the byte span owns the
        // original source, including the nested block's indentation.
        assert_eq!(source.get(start..end), Some(authored));
        assert_eq!(
            source[..start]
                .bytes()
                .filter(|byte| *byte == b'\n')
                .count() as u64
                + 1,
            line
        );
    }
}

#[test]
fn nested_claim_and_shadowed_helper_keep_their_actual_owners() {
    let document = build(SOURCE, true);
    let owner = strategy(&document);
    let execution = result(&document, owner.field("evidence"));
    let local_scope = resolve(&document, execution.field("fields").field("local_env"));
    let children = document.field("statements").as_array().unwrap();
    let helper = children
        .iter()
        .find(|s| {
            s.field("parent_statement_id") == owner.field("id")
                && s.field("statement_kind").as_str().ok()
                    == Some("Definition.DefineObj.HaveObjEqualStmt")
        })
        .unwrap();
    assert_eq!(helper.field("scope_id"), local_scope.field("scope_id"));
    assert!(!helper
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    for id in helper.field("produced_fact_ids").as_array().unwrap() {
        let fact = document
            .field("facts")
            .as_array()
            .unwrap()
            .iter()
            .find(|fact| fact.field("id") == id)
            .unwrap();
        assert_eq!(fact.field("producer_statement_id"), helper.field("id"));
        assert_eq!(fact.field("scope_id"), local_scope.field("scope_id"));
    }
    let claim = children
        .iter()
        .find(|s| {
            s.field("parent_statement_id") == owner.field("id")
                && s.field("statement_kind").as_str().ok() == Some("ProofBlock.ClaimStmt")
        })
        .unwrap();
    let nested = children
        .iter()
        .find(|s| s.field("parent_statement_id") == claim.field("id"))
        .unwrap();
    assert_eq!(nested.field("statement_kind").as_str().unwrap(), "Fact");
    assert_eq!(nested.field("status").as_str().unwrap(), "accepted");
    assert_ne!(nested.field("scope_id"), local_scope.field("scope_id"));
    let outer = children
        .iter()
        .find(|s| {
            s.field("parent_statement_id") == &JsonValue::Null
                && s.field("statement_kind").as_str().ok()
                    == Some("Definition.DefineObj.HaveObjEqualStmt")
        })
        .unwrap();
    let local_ids: BTreeSet<_> = helper
        .field("declaration_symbol_ids")
        .as_array()
        .unwrap()
        .iter()
        .map(|id| id.as_str().unwrap())
        .collect();
    let outer_ids: BTreeSet<_> = outer
        .field("declaration_symbol_ids")
        .as_array()
        .unwrap()
        .iter()
        .map(|id| id.as_str().unwrap())
        .collect();
    assert!(!local_ids.is_empty() && !outer_ids.is_empty());
    assert!(
        local_ids.is_disjoint(&outer_ids),
        "equal spelling does not merge local and outer definitions"
    );
}

#[test]
fn source_mapping_does_not_export_witnesses_or_prove_a_false_instance() {
    let document = build(&format!("{SOURCE}\nu $in R\n"), false);
    assert_eq!(
        strategy(&document).field("status").as_str().unwrap(),
        "accepted"
    );
    let document = build(&format!("{SOURCE}\n$same(1)\nhelper = 1\n"), false);
    let rows = document.field("statements").as_array().unwrap();
    let rejected = rows
        .iter()
        .find(|s| s.field("text").as_str().ok() == Some("$same(1)"))
        .unwrap();
    assert_eq!(rejected.field("status").as_str().unwrap(), "rejected");
    assert!(rejected
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    let last = rows.last().unwrap();
    assert_eq!(last.field("status").as_str().unwrap(), "accepted");
    assert_eq!(last.field("text").as_str().unwrap(), "helper = 1");
}

#[test]
fn a_failed_nested_strategy_cannot_borrow_the_successful_body() {
    let document = build(
        include_str!(
            "../examples/test_statements/negative/def_strategy_stmt/false-nested-proof.lit"
        ),
        false,
    );
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
    for child in document.field("statements").as_array().unwrap() {
        if child.field("statement_kind").as_str().ok() == Some("Fact")
            && child.field("text").as_str().ok() == Some("x = 0")
        {
            assert_ne!(child.field("status").as_str().ok(), Some("accepted"));
        }
    }
}
