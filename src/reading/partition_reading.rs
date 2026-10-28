//! Package one reading document for lazy source/proof loading. Identity and
//! verdicts stay those of the complete bundle; parts never re-derive evidence.
use crate::prelude::*;
use std::collections::{BTreeMap, BTreeSet};

use super::helper::{digest, object, text};

pub(super) struct ReadingSite {
    pub manifest: JsonValue,
    pub files: BTreeMap<String, String>,
}

impl ReadingSite {
    pub fn new(document: &JsonValue) -> Self {
        let fields = document.as_object().expect("reading document is an object");
        let array = |name: &str| {
            fields
                .get(name)
                .and_then(|value| value.as_array().ok())
                .unwrap_or(&[])
        };
        let sources = array("sources");
        let statements = array("statements");
        let facts = array("facts");
        let inferences = array("inferences");
        let wd = array("well_definedness");
        let nodes = array("evidence_nodes");
        let occurrences = array("occurrences");
        let complete = document.stringify();
        let manifest_id = digest(&complete);
        let directory = format!(
            "reading-data/{}",
            manifest_id.trim_start_matches("fnv1a64:")
        );
        let statement_sources = statements
            .iter()
            .map(|value| (field(value, "id"), field(value, "source_id")))
            .collect::<BTreeMap<_, _>>();
        let evidence = nodes
            .iter()
            .map(|value| (field(value, "id"), value))
            .collect::<BTreeMap<_, _>>();
        let mut files = BTreeMap::new();
        let full_url = format!("{directory}/reading.json");
        files.insert(full_url.clone(), complete);
        let mut manifest = without(
            document,
            &[
                "sources",
                "statements",
                "facts",
                "inferences",
                "well_definedness",
                "occurrences",
                "evidence_nodes",
            ],
        );
        let mut source_index = Vec::new();
        let mut search = Vec::new();
        for (index, source) in sources.iter().enumerate() {
            let id = field(source, "id");
            let url = format!("{directory}/part{index}.json");
            let source_url = format!("{directory}/source{index}.json");
            let mut metadata = without(source, &["content", "tokens"]);
            insert(&mut metadata, "chunk_url", text(&url));
            insert(&mut metadata, "source_url", text(&source_url));
            source_index.push(metadata);
            files.insert(
                source_url,
                object(vec![
                    ("kind", text("reading_source")),
                    ("manifest_id", text(&manifest_id)),
                    ("source", without(source, &["tokens"])),
                ])
                .stringify(),
            );
            let owned = |value: &JsonValue| {
                statement_sources
                    .get(&field(value, "producer_statement_id"))
                    .cloned()
                    .unwrap_or_else(|| field(value, "source_id"))
                    == id
            };
            let chapter_statements = statements
                .iter()
                .filter(|value| field(value, "source_id") == id)
                .cloned()
                .collect::<Vec<_>>();
            let chapter_facts = facts
                .iter()
                .filter(|value| owned(value))
                .cloned()
                .collect::<Vec<_>>();
            let chapter_inferences = inferences
                .iter()
                .filter(|value| owned(value))
                .cloned()
                .collect::<Vec<_>>();
            let chapter_wd = wd
                .iter()
                .filter(|value| owned(value))
                .cloned()
                .collect::<Vec<_>>();
            let mut seen = BTreeSet::new();
            let mut pending = chapter_statements
                .iter()
                .chain(&chapter_facts)
                .chain(&chapter_inferences)
                .chain(&chapter_wd)
                .collect::<Vec<_>>();
            while let Some(value) = pending.pop() {
                match value {
                    JsonValue::Array(values) => pending.extend(values),
                    JsonValue::Object(fields) => {
                        if field(value, "kind") == "evidence_reference" {
                            let reference = field(value, "evidence_id");
                            if seen.insert(reference.clone()) {
                                if let Some(entry) = evidence.get(&reference) {
                                    if let Some(node) =
                                        entry.as_object().ok().and_then(|fields| fields.get("node"))
                                    {
                                        pending.push(node);
                                    }
                                }
                            }
                        } else {
                            pending.extend(fields.iter().map(|(_, value)| value));
                        }
                    }
                    _ => {}
                }
            }
            let chapter_nodes = seen
                .iter()
                .filter_map(|id| evidence.get(id).map(|value| (*value).clone()))
                .collect();
            let part = object(vec![
                ("kind", text("reading_chunk")),
                ("manifest_id", text(&manifest_id)),
                ("source_id", text(&id)),
                ("sources", JsonValue::Array(vec![source.clone()])),
                ("statements", JsonValue::Array(chapter_statements)),
                ("facts", JsonValue::Array(chapter_facts)),
                ("inferences", JsonValue::Array(chapter_inferences)),
                ("well_definedness", JsonValue::Array(chapter_wd)),
                ("evidence_nodes", JsonValue::Array(chapter_nodes)),
                (
                    "occurrences",
                    JsonValue::Array(
                        occurrences
                            .iter()
                            .filter(|value| field(value, "source_id") == id)
                            .cloned()
                            .collect(),
                    ),
                ),
            ]);
            files.insert(url, part.stringify());
            let content = field(source, "content");
            let mut offset = 0;
            for (line_index, line) in content.split('\n').enumerate() {
                if !line.trim().is_empty() {
                    let owner = statements
                        .iter()
                        .filter(|value| {
                            field(value, "source_id") == id
                                && number(value, "line") <= line_index + 1
                                && number(value, "end_byte") > offset
                        })
                        .min_by_key(|value| {
                            (
                                number(value, "end_byte")
                                    .saturating_sub(number(value, "start_byte")),
                                field(value, "id") != field(value, "source_statement_id"),
                            )
                        });
                    search.push(object(vec![
                        ("source_id", text(&id)),
                        ("line", JsonValue::Number((line_index + 1) as f64)),
                        ("text", text(line.trim_end_matches('\r'))),
                        (
                            "statement_id",
                            owner
                                .map(|value| text(&field(value, "source_statement_id")))
                                .unwrap_or(JsonValue::Null),
                        ),
                    ]));
                }
                offset += line.len() + 1;
            }
        }
        let occurrences_url = format!("{directory}/occurrences.json");
        files.insert(
            occurrences_url.clone(),
            object(vec![
                ("kind", text("reading_occurrences")),
                ("manifest_id", text(&manifest_id)),
                ("occurrences", JsonValue::Array(occurrences.to_vec())),
            ])
            .stringify(),
        );
        let search_url = format!("{directory}/search.json");
        files.insert(
            search_url.clone(),
            object(vec![
                ("kind", text("reading_search")),
                ("manifest_id", text(&manifest_id)),
                ("entries", JsonValue::Array(search)),
            ])
            .stringify(),
        );
        for (key, value) in [
            ("kind", text("reading_manifest")),
            ("manifest_id", text(&manifest_id)),
            ("full_document_url", text(&full_url)),
            ("occurrences_url", text(&occurrences_url)),
            ("search_url", text(&search_url)),
            ("sources", JsonValue::Array(source_index)),
            (
                "statements",
                JsonValue::Array(
                    statements
                        .iter()
                        .map(|value| without(value, &["evidence", "source_text"]))
                        .collect(),
                ),
            ),
            (
                "facts",
                JsonValue::Array(
                    facts
                        .iter()
                        .map(|value| without(value, &["evidence"]))
                        .collect(),
                ),
            ),
            (
                "inferences",
                JsonValue::Array(
                    inferences
                        .iter()
                        .map(|value| without(value, &["evidence"]))
                        .collect(),
                ),
            ),
            (
                "well_definedness",
                JsonValue::Array(
                    wd.iter()
                        .map(|value| without(value, &["evidence", "registration"]))
                        .collect(),
                ),
            ),
        ] {
            insert(&mut manifest, key, value);
        }
        files.insert("reading.manifest.json".into(), manifest.stringify());
        Self { manifest, files }
    }
}

fn field(value: &JsonValue, name: &str) -> String {
    value
        .as_object()
        .ok()
        .and_then(|fields| fields.get(name))
        .and_then(|value| value.as_str().ok())
        .unwrap_or("")
        .into()
}

fn number(value: &JsonValue, name: &str) -> usize {
    value
        .as_object()
        .ok()
        .and_then(|fields| fields.get(name))
        .and_then(|value| value.as_u64().ok())
        .unwrap_or(0) as usize
}

fn without(value: &JsonValue, names: &[&str]) -> JsonValue {
    JsonValue::object_from(
        value
            .as_object()
            .expect("reading record is an object")
            .iter()
            .filter(|(key, _)| !names.contains(&key.as_str()))
            .map(|(key, value)| (key.clone(), value.clone()))
            .collect(),
    )
}

fn insert(value: &mut JsonValue, name: &str, field: JsonValue) {
    if let JsonValue::Object(fields) = value {
        fields.insert(name.into(), field);
    }
}
