use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, ReadingInput};
use std::collections::BTreeSet;

#[test]
fn structured_induction_titles_keep_original_utf8_source_ranges() {
    let source = format!(
        "# 原始位置：? from and ? induc in comments are not anchors.\n{}",
        include_str!("../examples/stmt_nodes/by/induction_domain_and_proof_actions.lit")
    );
    let result = build_reading(
        &ReadingInput::Source(source.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let mut structured = 0;
    let mut unstructured = 0;
    for statement in result.document.field("statements").as_array().unwrap() {
        if statement.field("statement_kind").as_str().ok() != Some("By.ByInducStmt") {
            continue;
        }
        let Some(anchors) = statement.as_object().unwrap().get("block_anchors") else {
            unstructured += 1;
            continue;
        };
        let anchors = anchors.as_array().unwrap();
        structured += 1;
        assert_eq!(anchors.len(), 2);
        let mut roles = BTreeSet::new();
        for anchor in anchors {
            let start = anchor.field("start_byte").as_u64().unwrap() as usize;
            let end = anchor.field("end_byte").as_u64().unwrap() as usize;
            let text = anchor.field("source_text").as_str().unwrap();
            let role = anchor.field("role").as_str().unwrap();
            assert_eq!(source.get(start..end), Some(text));
            assert_eq!(
                source[..start]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1,
                anchor.field("line").as_u64().unwrap() as usize
            );
            assert!(start >= statement.field("start_byte").as_u64().unwrap() as usize);
            assert!(end <= statement.field("end_byte").as_u64().unwrap() as usize);
            match role {
                "induction_base" => assert!(text.starts_with("? from ")),
                "induction_step" => assert_eq!(text, "? induc:"),
                _ => panic!("unexpected role: {role}"),
            }
            assert!(roles.insert(role));
        }
    }
    assert_eq!(structured, 2);
    assert_eq!(
        unstructured, 1,
        "a neighboring structured proof cannot supply another block's titles"
    );
}

#[test]
fn ordinary_statements_and_unstructured_induction_do_not_gain_titles() {
    for source in [
        include_str!("../examples/stmt_nodes/by/by_induc.lit"),
        include_str!("../examples/stmt_nodes/by/by_strong_induc.lit"),
        include_str!("../examples/stmt_nodes/by/by_cases.lit"),
    ] {
        let result = build_reading(
            &ReadingInput::Source(source.into()),
            true,
            OutputLanguage::English,
        );
        assert!(result.success);
        for statement in result.document.field("statements").as_array().unwrap() {
            assert!(statement
                .as_object()
                .unwrap()
                .get("block_anchors")
                .is_none());
        }
    }
}

#[test]
fn rejected_induction_retains_no_completed_output_or_borrowed_titles() {
    let result = build_reading(
        &ReadingInput::Source(
            include_str!("../examples/test_statements/negative/by_induc_stmt/false-base-case.lit")
                .into(),
        ),
        true,
        OutputLanguage::English,
    );
    assert!(!result.success);
    let statement = &result.document.field("statements").as_array().unwrap()[0];
    assert_eq!(statement.field("status").as_str().unwrap(), "rejected");
    assert!(statement
        .field("produced_fact_ids")
        .as_array()
        .unwrap()
        .is_empty());
    assert!(statement
        .as_object()
        .unwrap()
        .get("block_anchors")
        .is_none());
}

trait ReadingFields {
    fn field(&self, key: &str) -> &JsonValue;
}

#[test]
fn struct_fields_keep_typed_bindings_and_original_utf8_ranges() {
    let source = format!(
        "# 字段位置：注释里的 x R 不是字段。\n{}",
        include_str!("../examples/test_statements/def_struct_stmt.lit")
    );
    let result = build_reading(
        &ReadingInput::Source(source.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let document = &result.document;
    let mut structures = 0;
    for statement in document.field("statements").as_array().unwrap() {
        if statement.field("statement_kind").as_str().ok() != Some("Definition.DefStructStmt") {
            continue;
        }
        structures += 1;
        let definition = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row.field("node"))
            .find(|node| {
                node.as_object()
                    .unwrap()
                    .get("type")
                    .and_then(|v| v.as_str().ok())
                    == Some("DefStructStmt")
                    && node.field("declaration").field("statement_id") == statement.field("id")
            })
            .unwrap();
        let fields = definition
            .field("fields")
            .field("fields")
            .as_array()
            .unwrap();
        let anchors = statement.field("block_anchors").as_array().unwrap();
        assert_eq!(anchors.len(), fields.len());
        for (index, anchor) in anchors.iter().enumerate() {
            assert_eq!(anchor.field("role").as_str().unwrap(), "structure_field");
            assert_eq!(anchor.field("index").as_u64().unwrap() as usize, index);
            let field = resolve_reading_evidence(document, &fields[index]);
            assert_eq!(
                anchor.field("symbol_id"),
                field.field("fields").field("binding").field("symbol_id")
            );
            let start = anchor.field("start_byte").as_u64().unwrap() as usize;
            let end = anchor.field("end_byte").as_u64().unwrap() as usize;
            assert_eq!(
                source.get(start..end),
                anchor.field("source_text").as_str().ok()
            );
            assert_eq!(
                source[..start].bytes().filter(|b| *b == b'\n').count() + 1,
                anchor.field("line").as_u64().unwrap() as usize
            );
            assert!(start >= statement.field("start_byte").as_u64().unwrap() as usize);
            assert!(end <= statement.field("end_byte").as_u64().unwrap() as usize);
        }
    }
    assert_eq!(structures, 3);
}

#[test]
fn registered_struct_fields_locate_source_before_resolved_qualification() {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let project = std::env::temp_dir().join(format!(
        "litex-struct-anchors-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&project).unwrap();
    let source = "# 原始字段；注释中的 element Z 不是声明。\nstruct ScalarIdentity<S nonempty_set>:\n    zero S\n    add fn(x, y S) S\n    <=>:\n        forall x S:\n            add(zero, x) = x\n\nstruct IdentityCarrier<S nonempty_set>:\n    scalars &ScalarIdentity<S> # resolved type has an internal module qualifier\n    element S\n\nstruct Neighbor:\n    scalars R\n    element Z\n";
    std::fs::write(project.join("structures.lit"), source).unwrap();
    std::fs::write(
        project.join("proof.lit"),
        "forall p &structures::IdentityCarrier<R>:\n    p.element $in R\n",
    )
    .unwrap();
    std::fs::write(
        project.join("litex.config"),
        "[export]\nstructures=\"./structures.lit\"\nproof=\"./proof.lit\"\n",
    )
    .unwrap();
    let result = build_reading(
        &ReadingInput::Project(project.clone()),
        true,
        OutputLanguage::English,
    );
    std::fs::remove_dir_all(&project).unwrap();
    assert!(result.success, "{:?}", result.document);
    let document = &result.document;
    let statements = document.field("statements").as_array().unwrap();
    let mut count = 0;
    for statement in statements {
        if statement.field("statement_kind").as_str().unwrap() != "Definition.DefStructStmt" {
            continue;
        }
        let definition = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row.field("node"))
            .find(|node| {
                node.as_object()
                    .unwrap()
                    .get("type")
                    .and_then(|value| value.as_str().ok())
                    == Some("DefStructStmt")
                    && node.field("declaration").field("statement_id") == statement.field("id")
            })
            .unwrap();
        let fields = definition
            .field("fields")
            .field("fields")
            .as_array()
            .unwrap();
        let anchors = statement.field("block_anchors").as_array().unwrap();
        assert_eq!(anchors.len(), 2);
        for (index, anchor) in anchors.iter().enumerate() {
            let field = resolve_reading_evidence(document, &fields[index]);
            assert_eq!(
                anchor.field("symbol_id"),
                field.field("fields").field("binding").field("symbol_id")
            );
            assert_eq!(anchor.field("index").as_u64().unwrap() as usize, index);
            let start = anchor.field("start_byte").as_u64().unwrap() as usize;
            let end = anchor.field("end_byte").as_u64().unwrap() as usize;
            assert_eq!(
                source.get(start..end),
                anchor.field("source_text").as_str().ok()
            );
            assert_eq!(
                source[..start]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1,
                anchor.field("line").as_u64().unwrap() as usize
            );
            assert!(start >= statement.field("start_byte").as_u64().unwrap() as usize);
            assert!(end <= statement.field("end_byte").as_u64().unwrap() as usize);
            if statement.field("line").as_u64().unwrap() == 9 && index == 0 {
                assert_eq!(
                    anchor.field("source_text").as_str().unwrap(),
                    "scalars &ScalarIdentity<S>"
                );
                assert!(resolve_reading_evidence(
                    document,
                    field.field("fields").field("field_type")
                )
                .field("text")
                .as_str()
                .unwrap()
                .contains("::ScalarIdentity"));
            }
        }
        count += 1;
    }
    assert_eq!(
        count, 3,
        "the neighbor keeps its own similarly named fields"
    );
}

fn resolve_reading_evidence<'a>(
    document: &'a JsonValue,
    mut value: &'a JsonValue,
) -> &'a JsonValue {
    while value
        .as_object()
        .unwrap()
        .get("kind")
        .and_then(|v| v.as_str().ok())
        == Some("evidence_reference")
    {
        let id = value.field("evidence_id");
        value = document
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row.field("id") == id)
            .unwrap()
            .field("node");
    }
    value
}

impl ReadingFields for JsonValue {
    fn field(&self, key: &str) -> &JsonValue {
        self.as_object()
            .unwrap()
            .get(key)
            .unwrap_or_else(|| panic!("missing {key}"))
    }
}
