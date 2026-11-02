//! Failed definition folding retains the actual checked prefix and local scope.
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
fn resolve(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut value = value.clone();
    while value.field("kind").as_str().ok() == Some("evidence_reference") {
        value = document
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
fn unwrap(document: &JsonValue, value: &JsonValue) -> JsonValue {
    let mut node = resolve(document, value);
    while node.field("fields").field("0") != &JsonValue::Null {
        node = resolve(document, node.field("fields").field("0"));
    }
    node
}
fn nodes(document: &JsonValue, name: &str) -> Vec<JsonValue> {
    document
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row.field("node"))
        .filter(|node| node.field("type").as_str().ok() == Some(name))
        .cloned()
        .collect()
}

#[test]
fn user_and_builtin_definition_failures_keep_each_actual_preceding_check() {
    for (source, index, total) in [
        ("prop nonnegative(x R):\n    x >= 0\nby def $nonnegative(-1)\n", 1, 2),
        ("prop small_positive(x R):\n    x > 0\n    x < 1\n    x != 0\nby def $small_positive(2)\n", 2, 4),
        ("prop equals_one_in(A set,x A):\n    x=1\nby def $equals_one_in({1,2},2)\n", 2, 3),
        ("by def R $proper_subset R\n", 1, 2),
        ("by def $dvd(3,2)\n", 0, 2),
    ] {
        let built = build_reading(&ReadingInput::Source(source.into()), true, OutputLanguage::English);
        assert!(!built.success);
        let document = &built.document;
        let contexts = nodes(document, "ExecByDefLocalFailure");
        assert_eq!(contexts.len(), 1, "{source}");
        let context = &contexts[0];
        let failure = unwrap(document, context.field("fields").field("failure"));
        assert_eq!(failure.field("type").as_str().unwrap(), "DefinitionProofFailed");
        assert_eq!(failure.field("variant").as_str().unwrap(), "Requirement");
        let requirements = failure.field("fields").field("requirement_facts").as_array().unwrap();
        let checked = failure.field("fields").field("proof_of_requirement_facts").as_array().unwrap();
        assert_eq!(requirements.len(), total);
        assert_eq!(checked.len(), index);
        for (position, proof) in checked.iter().enumerate() {
            let result = unwrap(document, proof);
            assert!(result.field("type").as_str().unwrap().ends_with("Success"));
            assert_eq!(unwrap(document, result.field("fields").field("fact")), unwrap(document, &requirements[position]));
        }
        assert_eq!(unwrap(document, failure.field("fields").field("fact")), unwrap(document, &requirements[index]));
        let failed = unwrap(document, failure.field("fields").field("result"));
        assert!(failed.field("type").as_str().unwrap().ends_with("Failed"));
        assert_eq!(unwrap(document, failed.field("fields").field("fact")), unwrap(document, &requirements[index]));
        let statement = document.field("statements").as_array().unwrap().iter().find(|s|
            s.field("status").as_str().ok() == Some("rejected")
            && s.field("statement_kind").as_str().unwrap().ends_with("ByDefStmt")).unwrap();
        assert!(statement.field("produced_fact_ids").as_array().unwrap().is_empty());
        let local = resolve(document, context.field("fields").field("local_env"));
        let scope = document.field("scopes").as_array().unwrap().iter().find(|s| s.field("id") == local.field("scope_id")).unwrap();
        assert_eq!(scope.field("statement_id"), statement.field("id"));
        assert_eq!(scope.field("parent_id"), statement.field("scope_id"));
    }
}

#[test]
fn failed_nested_definition_does_not_publish_its_goal_or_close_the_parent() {
    let source = "prop small_positive(x R):\n    x>0\n    x<1\n    x!=0\nclaim:\n    ? forall x R:\n        x>0\n        =>:\n            $small_positive(x)\n    by def $small_positive(x)\n";
    let built = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!built.success);
    let document = &built.document;
    assert_eq!(nodes(document, "ExecByDefLocalFailure").len(), 1);
    assert_eq!(nodes(document, "ExecClaimLocalFailure").len(), 1);
    for statement in document.field("statements").as_array().unwrap() {
        if statement.field("status").as_str().ok() == Some("rejected") {
            assert!(statement
                .field("produced_fact_ids")
                .as_array()
                .unwrap()
                .is_empty());
        }
    }
}

#[test]
fn goal_formation_failure_never_claims_an_entered_definition_scope() {
    let built = build_reading(
        &ReadingInput::Source(
            "prop nonnegative(x R):\n    x>=0\nby def $nonnegative(1/0)\n".into(),
        ),
        true,
        OutputLanguage::English,
    );
    assert!(!built.success);
    assert!(nodes(&built.document, "ExecByDefLocalFailure").is_empty());
    assert!(!nodes(&built.document, "ExecByDefStmtFailed").is_empty());
}

#[test]
fn unavailable_definition_keeps_its_entered_context_without_requirement_proofs() {
    let built = build_reading(
        &ReadingInput::Source("abstract_prop no_definition(x)\nby def $no_definition(1)\n".into()),
        true,
        OutputLanguage::English,
    );
    assert!(!built.success);
    assert_eq!(nodes(&built.document, "ExecByDefLocalFailure").len(), 1);
    let failures = nodes(&built.document, "DefinitionProofFailed");
    assert_eq!(failures.len(), 1);
    assert_eq!(
        failures[0].field("variant").as_str().unwrap(),
        "Unavailable"
    );
}
