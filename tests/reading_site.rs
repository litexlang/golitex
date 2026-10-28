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
    assert!(statements.iter().all(|statement| !statement
        .field("statement_kind")
        .as_str()
        .unwrap()
        .is_empty()));
    assert!(statements.iter().any(
        |statement| statement.field("statement_kind").as_str().unwrap() == "Definition.DefThmStmt"
    ));
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
    assert!(html.contains("katex.min.js") && html.contains("katex.min.css"));
    let math_css = fs::read_to_string(directory.join("katex.min.css")).unwrap();
    assert!(math_css.contains("data:font/woff2;base64,") && !math_css.contains("url(fonts/"));
    assert!(fs::read_to_string(directory.join("katex.min.js"))
        .unwrap()
        .contains("KaTeX"));
    assert!(fs::read_to_string(directory.join("katex.LICENSE"))
        .unwrap()
        .contains("Permission is hereby granted"));
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
        let source_data = JsonValue::parse(
            &fs::read_to_string(directory.join(source.field("source_url").as_str().unwrap()))
                .unwrap(),
        )
        .unwrap();
        assert_eq!(
            source_data.field("kind").as_str().unwrap(),
            "reading_source"
        );
        assert_eq!(
            source_data.field("manifest_id"),
            manifest.field("manifest_id")
        );
        let original_source = full
            .field("sources")
            .as_array()
            .unwrap()
            .iter()
            .find(|value| value.field("id") == source.field("id"))
            .unwrap();
        for key in ["id", "path", "content"] {
            assert_eq!(
                source_data.field("source").field(key),
                original_source.field(key)
            );
        }
        assert!(source_data
            .field("source")
            .as_object()
            .unwrap()
            .get("tokens")
            .is_none());
        for key in ["statements", "facts", "evidence_nodes", "inferences"] {
            assert!(source_data.as_object().unwrap().get(key).is_none());
        }
        let part = JsonValue::parse(
            &fs::read_to_string(directory.join(source.field("chunk_url").as_str().unwrap()))
                .unwrap(),
        )
        .unwrap();
        assert_eq!(part.field("manifest_id"), manifest.field("manifest_id"));
        assert_eq!(part.field("source_id"), source.field("id"));
        for statement in part.field("statements").as_array().unwrap() {
            let original = statements
                .iter()
                .find(|original| original.field("id") == statement.field("id"))
                .unwrap();
            assert_eq!(
                statement.field("statement_kind"),
                original.field("statement_kind")
            );
            assert_eq!(
                statement.field("mathematics"),
                original.field("mathematics")
            );
        }
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

#[test]
fn localized_titles_survive_export_without_changing_proofs() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "litex-reading-titles-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let source = directory.join("chapter.lit");
    fs::write(&source, "1 = 1\n").unwrap();
    let before = build_reading(
        &ReadingInput::File(source.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(before.success);
    let labels = directory.join("reading-titles.json");
    fs::write(&labels, r#"{"kind":"reading_titles","sources":{"chapter.lit":{"zh":"一个等式","en":"An equality"},"other.lit":{"zh":"另一个例子"}}}"#).unwrap();
    let after = build_reading(
        &ReadingInput::File(source.clone()),
        true,
        OutputLanguage::English,
    );
    assert!(after.success);
    for key in ["statements", "facts", "occurrences", "input_digest"] {
        assert_eq!(
            before.document.field(key),
            after.document.field(key),
            "{key}"
        );
    }
    let record = &after.document.field("sources").as_array().unwrap()[0];
    assert_eq!(
        record.field("titles").field("zh").as_str().unwrap(),
        "一个等式"
    );
    assert_eq!(
        record.field("titles").field("en").as_str().unwrap(),
        "An equality"
    );
    assert_eq!(record.field("path").as_str().unwrap(), "chapter.lit");
    assert_ne!(
        before.document.field("bundle_id"),
        after.document.field("bundle_id")
    );
    let site = directory.join("site");
    export_reading(&site, &after.document).unwrap();
    let manifest =
        JsonValue::parse(&fs::read_to_string(site.join("reading.manifest.json")).unwrap()).unwrap();
    assert_eq!(
        manifest.field("sources").as_array().unwrap()[0].field("titles"),
        record.field("titles")
    );
    // Missing, unrelated, malformed or oversized sidecars cannot change a proof.
    for content in [
        "not JSON".into(),
        r#"{"kind":"reading_titles","sources":{"other.lit":{"en":"Other"}}}"#.into(),
        " ".repeat(65_537),
    ] {
        fs::write(&labels, content).unwrap();
        let fallback = build_reading(
            &ReadingInput::File(source.clone()),
            true,
            OutputLanguage::English,
        );
        assert!(fallback.success);
        assert!(fallback.document.field("sources").as_array().unwrap()[0]
            .as_object()
            .unwrap()
            .get("titles")
            .is_none());
        assert_eq!(
            before.document.field("facts"),
            fallback.document.field("facts")
        );
    }
    fs::remove_dir_all(directory).unwrap();
}
