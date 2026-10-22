//! Real project → portable JSON + lazy site parts; no fabricated proof edges.
use litex::knowledge_base::JsonValue;
use litex::launch_command::OutputLanguage;
use litex::reading::{build_reading, export_reading, ReadingInput};
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

trait Fields {
    fn field(&self, name: &str) -> &JsonValue;
}
impl Fields for JsonValue {
    fn field(&self, name: &str) -> &JsonValue {
        self.as_object().unwrap().get(name).unwrap()
    }
}

#[test]
fn site_chapters_preserve_the_complete_bundle_and_reference_closure() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/reading/book");
    let result = build_reading(
        &ReadingInput::Project(project),
        true,
        OutputLanguage::English,
    );
    assert!(result.success);
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("litex-reading-site-{}-{nonce}", std::process::id()));
    export_reading(&directory, &result.document).unwrap();
    let manifest =
        JsonValue::parse(&fs::read_to_string(directory.join("reading.manifest.json")).unwrap())
            .unwrap();
    assert_eq!(manifest.field("kind").as_str().unwrap(), "reading_manifest");
    assert!(manifest
        .as_object()
        .unwrap()
        .get("evidence_nodes")
        .is_none());
    let full = JsonValue::parse(
        &fs::read_to_string(directory.join(manifest.field("full_document_url").as_str().unwrap()))
            .unwrap(),
    )
    .unwrap();
    assert_eq!(full, result.document);
    let statements = full.field("statements").as_array().unwrap();
    let application = statements
        .iter()
        .find(|value| {
            value.field("source_id").as_str().unwrap() == "source1"
                && value.field("line").as_u64().unwrap() == 1
        })
        .unwrap();
    assert!(
        application
            .field("declaration_dependencies")
            .as_array()
            .unwrap()
            .contains(statements[0].field("id")),
        "the actual checked predicate signature links by-def to its source declaration"
    );
    let named_origin = full
        .field("inferences")
        .as_array()
        .unwrap()
        .iter()
        .filter(|inference| inference.field("producer_statement_id") == application.field("id"))
        .flat_map(|inference| inference.field("conclusion_origins").as_array().unwrap())
        .find(|origin| origin.field("kind").as_str().unwrap() == "definition")
        .expect("actual by-def output retains its expansion origin");
    assert_eq!(
        named_origin.field("definition_statement_id"),
        statements[0].field("id")
    );
    assert_eq!(
        named_origin.field("source_symbol_id").as_str().unwrap(),
        "named:01-definitions.lit:above_zero"
    );
    let portable =
        JsonValue::parse(&fs::read_to_string(directory.join("reading.json")).unwrap()).unwrap();
    assert_eq!(portable, full);
    let html = fs::read_to_string(directory.join("index.html")).unwrap();
    assert!(html.contains("reading_manifest") && html.contains("standalone.html"));
    assert!(fs::read_to_string(directory.join("standalone.html"))
        .unwrap()
        .contains("\"evidence_nodes\""));
    let facts = manifest
        .field("facts")
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.field("id").as_str().unwrap())
        .collect::<BTreeSet<_>>();
    let wd = manifest
        .field("well_definedness")
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.field("id").as_str().unwrap())
        .collect::<BTreeSet<_>>();
    let mut loaded = BTreeSet::new();
    for source in manifest.field("sources").as_array().unwrap() {
        assert!(source.as_object().unwrap().get("content").is_none());
        let part = JsonValue::parse(
            &fs::read_to_string(directory.join(source.field("chunk_url").as_str().unwrap()))
                .unwrap(),
        )
        .unwrap();
        assert_eq!(part.field("manifest_id"), manifest.field("manifest_id"));
        assert_eq!(part.field("source_id"), source.field("id"));
        assert!(!part.field("sources").as_array().unwrap()[0]
            .field("content")
            .as_str()
            .unwrap()
            .is_empty());
        let nodes = part
            .field("evidence_nodes")
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.field("id").as_str().unwrap())
            .collect::<BTreeSet<_>>();
        loaded.extend(nodes.iter().map(|id| id.to_string()));
        let mut pending = vec![&part];
        while let Some(value) = pending.pop() {
            match value {
                JsonValue::Array(values) => pending.extend(values),
                JsonValue::Object(fields) => {
                    match fields.get("kind").and_then(|value| value.as_str().ok()) {
                        Some("evidence_reference") => {
                            assert!(nodes.contains(value.field("evidence_id").as_str().unwrap()))
                        }
                        Some("fact_reference") => {
                            assert!(facts.contains(value.field("fact_id").as_str().unwrap()))
                        }
                        Some("well_definedness_reference" | "well_definedness_identity") => {
                            assert!(wd.contains(value.field("id").as_str().unwrap()))
                        }
                        _ => {}
                    }
                    pending.extend(fields.iter().map(|(_, value)| value));
                }
                _ => {}
            }
        }
    }
    let all_nodes = full
        .field("evidence_nodes")
        .as_array()
        .unwrap()
        .iter()
        .map(|node| node.field("id").as_str().unwrap().to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        loaded, all_nodes,
        "every exported typed node is retained across the chapters"
    );
    let search = JsonValue::parse(
        &fs::read_to_string(directory.join(manifest.field("search_url").as_str().unwrap()))
            .unwrap(),
    )
    .unwrap();
    assert!(search
        .field("entries")
        .as_array()
        .unwrap()
        .iter()
        .any(|entry| entry
            .field("text")
            .as_str()
            .unwrap()
            .contains("Chapter 3: local proof")));
    assert!(
        manifest
            .field("statements")
            .as_array()
            .unwrap()
            .iter()
            .any(|statement| !statement
                .field("declaration_dependencies")
                .as_array()
                .unwrap()
                .is_empty()),
        "named cross-chapter interfaces must retain real declaration links"
    );
    fs::remove_dir_all(directory).unwrap();
}
