//! Concise per-submission feedback; standalone projections retain full evidence.

use super::helper::{object, statement_result_value, string};
use super::json_keys::localize_key;
use crate::knowledge_base::JsonObject;
use crate::prelude::*;

/// Stable, read-only failure metadata for non-JSON consumers such as Reading.
/// Reuse the Normal projection's actual failure path and authored diagnostic;
/// never select a successful premise/WD child as the rejected obligation.
pub(crate) fn statement_failure_summary(
    result: &ExecStmtResult,
    runtime: &Runtime,
) -> Option<JsonValue> {
    if !result.is_failed() {
        return None;
    }
    let language = super::helper::output_language(runtime);
    let normal = super::project_stmt_normal(result, runtime);
    let reason = normal
        .as_object()
        .ok()?
        .get(&localize_key("why_failed", language))?;
    let mut localized = JsonValue::Object(JsonObject::new());
    summarize_failure(&mut localized, reason, language);
    let localized = localized.as_object().ok()?;
    let mut fields = JsonObject::new();
    for key in [
        "phase",
        "goal",
        "message",
        "cause",
        "index",
        "step_index",
        "branch_index",
        "then_index",
        "expected",
        "actual",
        "failed_statement",
        "category",
        "expression",
        "obligation",
    ] {
        if let Some(value) = localized.get(&localize_key(key, language)) {
            fields.insert(key.into(), value.clone());
        }
    }
    if let Some(location) = localized
        .get(&localize_key("source_location", language))
        .and_then(|value| value.as_object().ok())
    {
        let mut stable = JsonObject::new();
        for key in ["path", "line", "column"] {
            if let Some(value) = location.get(&localize_key(key, language)) {
                stable.insert(key.into(), value.clone());
            }
        }
        fields.insert("source_location".into(), JsonValue::Object(stable));
    }
    (!fields.is_empty()).then_some(JsonValue::Object(fields))
}

pub(super) fn summarize_statements(
    statements: Vec<JsonValue>,
    language: OutputLanguage,
) -> (Vec<JsonValue>, Vec<JsonValue>) {
    let mut results = Vec::with_capacity(statements.len());
    let mut errors = Vec::new();
    for (index, statement) in statements.into_iter().enumerate() {
        let fields = statement.as_object().unwrap();
        if fields
            .get(&localize_key("statement_result", language))
            .and_then(|value| value.as_str().ok())
            != Some("rejected")
        {
            results.push(statement);
            continue;
        }
        let source = fields
            .get(&localize_key("statement", language))
            .cloned()
            .unwrap_or_else(|| string(""));
        let mut error = object(
            language,
            vec![
                ("statement_index", JsonValue::Number(index as f64)),
                ("statement", source.clone()),
            ],
        );
        if let Some(reason) = fields.get(&localize_key("why_failed", language)) {
            summarize_failure(&mut error, reason, language);
        }
        errors.push(error);
        results.push(object(
            language,
            vec![
                ("statement_result", statement_result_value(false)),
                ("statement", source),
            ],
        ));
    }
    (results, errors)
}

pub(super) fn input_failure(
    input: &crate::run::run_command_outcome::RunInputError,
    language: OutputLanguage,
) -> JsonValue {
    let error = &input.error;
    let mut location = object(
        language,
        vec![
            ("path", string(error.path.to_string())),
            ("line", JsonValue::Number(error.line as f64)),
        ],
    );
    if let Some(column) = error.source.as_ref().and_then(|source| source.column) {
        if let JsonValue::Object(fields) = &mut location {
            fields.insert(
                localize_key("column", language),
                JsonValue::Number(column as f64),
            );
        }
    }
    object(
        language,
        vec![
            ("statement_result", statement_result_value(false)),
            ("statement", string(&input.statement)),
            (
                "why_failed",
                object(
                    language,
                    vec![
                        ("phase", string("parse")),
                        ("message", string(&error.message)),
                        ("source_location", location),
                    ],
                ),
            ),
        ],
    )
}

fn summarize_failure(summary: &mut JsonValue, reason: &JsonValue, language: OutputLanguage) {
    let JsonValue::Object(summary) = summary else {
        return;
    };
    let mut current = reason;
    while let Ok(fields) = current.as_object() {
        for name in [
            "phase",
            "goal",
            "message",
            "cause",
            "index",
            "step_index",
            "branch_index",
            "then_index",
            "expected",
            "actual",
            "source_location",
            "returned_conclusions",
        ] {
            let key = localize_key(name, language);
            if let Some(value) = fields.get(&key) {
                if name == "goal"
                    && (value.as_str().ok() == Some("<well_defined_not_proven>")
                        || summary.get(&localize_key("statement", language)) == Some(value))
                {
                    continue;
                }
                if matches!(value, JsonValue::Object(_) | JsonValue::Array(_))
                    && name != "source_location"
                    && name != "returned_conclusions"
                {
                    continue;
                }
                summary.insert(key, value.clone());
            }
        }
        if let Some(statement) = fields.get(&localize_key("statement", language)) {
            summary.insert(
                localize_key("failed_statement", language),
                statement.clone(),
            );
        }
        if let Some(diagnostic) = fields
            .get(&localize_key("diagnostic", language))
            .and_then(|value| value.as_object().ok())
        {
            for name in ["category", "message", "expression", "obligation"] {
                let key = localize_key(name, language);
                if let Some(value) = diagnostic.get(&key) {
                    summary.insert(key, value.clone());
                }
            }
        }
        // Only follow the actual execution failure, never successful WD children
        // or the full verification tree. Nested proof bodies retain their location.
        if let Some(child) = fields.get(&localize_key("failure", language)) {
            current = child;
        } else if let Some(child) = fields
            .get(&localize_key("result", language))
            .filter(|child| {
                child
                    .as_object()
                    .ok()
                    .and_then(|fields| fields.get(&localize_key("statement_result", language)))
                    .and_then(|value| value.as_str().ok())
                    == Some("rejected")
            })
        {
            current = child;
        } else {
            break;
        }
    }
}
