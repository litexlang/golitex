//! Retained failed body results belong to their exact original source child.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};

fn document(source: &str) -> JsonValue {
    let result = build_reading(
        &ReadingInput::Source(source.into()),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    result.document
}
fn field<'a>(value: &'a JsonValue, key: &str) -> &'a JsonValue {
    value.as_object().unwrap().get(key).unwrap()
}
fn line(document: &JsonValue, number: u64) -> &JsonValue {
    field(document, "statements")
        .as_array()
        .unwrap()
        .iter()
        .find(|statement| field(statement, "line").as_u64().unwrap() == number)
        .unwrap()
}
fn status(document: &JsonValue, number: u64) -> &str {
    field(line(document, number), "status").as_str().unwrap()
}

#[test]
fn failed_calls_in_claim_theorem_and_contradiction_get_exact_source_verdicts() {
    for header in ["claim:", "thm failed_sum:"] {
        let source = format!("{header}\n    ? forall a,b seq(R),L,M R:\n        1 = 1\n    release thm seq_limit_add(a,b,L,M)\n    2 = 2\n");
        let data = document(&source);
        assert_eq!(status(&data, 1), "rejected");
        assert_eq!(status(&data, 4), "rejected");
        assert_eq!(status(&data, 5), "not_exported");
        let child = line(&data, 4);
        assert_eq!(
            field(child, "parent_statement_id"),
            field(line(&data, 1), "id")
        );
        assert!(field(child, "produced_fact_ids")
            .as_array()
            .unwrap()
            .is_empty());
        assert_eq!(
            field(field(child, "failure"), "phase").as_str().unwrap(),
            "premise"
        );
        assert_eq!(
            field(field(child, "evidence"), "kind").as_str().unwrap(),
            "evidence_reference"
        );
    }
    let data = document("by contra:\n    ? 2 = 3\n    1 = 2\n    4 = 4\n    impossible 2 != 3\n");
    assert_eq!(status(&data, 3), "rejected");
    assert_eq!(status(&data, 4), "not_exported");
}

#[test]
fn nested_failures_follow_actual_parent_chain_and_leave_suffix_without_verdict() {
    let data = document("claim:\n    ? 1 = 1\n    claim:\n        ? 1 = 1\n        1 = 2\n        3 = 3\n    4 = 4\n");
    for number in [1, 3, 5] {
        assert_eq!(status(&data, number), "rejected");
    }
    for number in [6, 7] {
        assert_eq!(status(&data, number), "not_exported");
    }
    assert_eq!(
        field(line(&data, 5), "parent_statement_id"),
        field(line(&data, 3), "id")
    );
    assert_eq!(
        field(line(&data, 3), "parent_statement_id"),
        field(line(&data, 1), "id")
    );
}

#[test]
fn goal_wd_and_conclusion_failures_do_not_invent_failed_body_steps() {
    let data = document("claim:\n    ? 1 / 0 = 0\n    1 = 2\n");
    assert_eq!(status(&data, 1), "rejected");
    assert_eq!(status(&data, 3), "not_exported");
    let data = document("claim:\n    ? 1 = 2\n    1 = 1\n");
    assert_eq!(status(&data, 1), "rejected");
    assert_eq!(status(&data, 3), "accepted");
}
