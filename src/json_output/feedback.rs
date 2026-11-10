//! Concise per-submission feedback; standalone projections retain full evidence.

use super::helper::{object, statement_result_value, string};
use super::json_keys::localize_key;
use crate::knowledge_base::JsonObject;
use crate::prelude::*;
use crate::run::RunSessionError;
use crate::runtime::RuntimeParseError;

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
    offset: usize,
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
                (
                    "statement_index",
                    JsonValue::Number((offset + index) as f64),
                ),
                ("statement", source.clone()),
            ],
        );
        if let Some(reason) = fields.get(&localize_key("why_failed", language)) {
            summarize_failure(&mut error, reason, language);
        }
        errors.push(error);
        let hidden = ["why_failed", "stores", "infers"].map(|key| localize_key(key, language));
        results.push(JsonValue::object_from(
            fields
                .iter()
                .filter(|(key, _)| !hidden.contains(key))
                .map(|(key, value)| (key.clone(), value.clone()))
                .collect(),
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

/// Summarize rejected inputs against the exact physical source snapshot.
pub(crate) fn source_errors(run: &RunLitexCodeResult, runtime: &Runtime) -> Vec<JsonValue> {
    let language = super::helper::output_language(runtime);
    let mut errors = Vec::new();
    for index in run.failed_statement_results.iter().flatten().copied() {
        let result = &run.statement_results[index];
        let diagnostic = statement_failure_summary(result, runtime);
        let details = diagnostic.as_ref().and_then(|value| value.as_object().ok());
        let mut error = JsonObject::new();
        if let Some(details) = details {
            for key in [
                "phase",
                "category",
                "expression",
                "obligation",
                "message",
                "cause",
            ] {
                if let Some(value) = details.get(key) {
                    error.insert(localize_key(key, language), value.clone());
                }
            }
            if error.get(&localize_key("obligation", language)).is_none() {
                if let Some(goal) = details.get("goal") {
                    error.insert(localize_key("obligation", language), goal.clone());
                }
            }
        }
        let located = super::source::failed_statement_line(result);
        let diagnostic_location = details
            .and_then(|details| details.get("source_location"))
            .and_then(|value| value.as_object().ok());
        let diagnostic_line = diagnostic_location
            .and_then(|location| location.get("line"))
            .and_then(|line| match line {
                JsonValue::Number(line) => Some(*line as usize),
                _ => None,
            });
        let statement_line = run
            .source
            .as_ref()
            .and_then(|source| source.statements.get(index).copied());
        let line = located
            .as_ref()
            .map(|position| position.line)
            .or(diagnostic_line)
            .or(statement_line);
        let file = located
            .as_ref()
            .map(|position| position.origin.to_string())
            .or_else(|| {
                diagnostic_location
                    .and_then(|location| location.get("path"))
                    .and_then(|value| value.as_str().ok())
                    .map(str::to_owned)
            })
            .or_else(|| run.source.as_ref().map(|source| source.origin.to_string()));
        let raw_line = run.source.as_ref().and_then(|source| {
            (file.as_deref() == Some(source.origin.to_string().as_str()))
                .then(|| source.line(line?))
                .flatten()
        });
        if let Some(file) = file {
            error.insert(localize_key("file", language), string(file));
        }
        if let Some(line) = line {
            error.insert(
                localize_key("line", language),
                JsonValue::Number(line as f64),
            );
        }
        if let Some(raw_line) = raw_line {
            error.insert(localize_key("source", language), string(raw_line));
        } else if let Some(statement) = run.statement_texts.get(index) {
            error.insert(localize_key("statement", language), string(statement));
        }
        let only_block_header = line == statement_line
            && run.source.as_ref().zip(line).is_some_and(|(source, line)| {
                source.block(line).is_some_and(|text| text.contains('\n'))
            });
        if diagnostic_line.is_none() && (located.is_none() || only_block_header) {
            error.insert(
                localize_key("location_precision", language),
                string("statement"),
            );
        }
        if error.get(&localize_key("message", language)).is_none() {
            error.insert(
                localize_key("message", language),
                string("The statement was rejected."),
            );
        }
        errors.push(JsonValue::Object(error));
    }
    if let Some(input) = &run.input_error {
        errors.push(parse_error(&input.error, run.source.as_ref(), language));
    }
    errors
}

pub(super) fn session_errors(
    error: &RunSessionError,
    path: Option<&std::path::Path>,
    language: OutputLanguage,
) -> Vec<JsonValue> {
    match error {
        RunSessionError::Runtime(error) => vec![runtime_error(error, path, language)],
        RunSessionError::FailToImport(failure) if !failure.rejected_feedback.is_empty() => {
            failure.rejected_feedback.clone()
        }
        RunSessionError::FailToImport(failure) => vec![object(
            language,
            vec![
                ("file", string(failure.path.display().to_string())),
                ("phase", string("import")),
                ("message", string(error.to_string())),
            ],
        )],
    }
}

pub(super) fn runtime_error(
    error: &RuntimeError,
    path: Option<&std::path::Path>,
    language: OutputLanguage,
) -> JsonValue {
    if let RuntimeError::ParseError(error) = error {
        return parse_error(error, None, language);
    }
    let mut fields = vec![
        ("phase", string("runtime")),
        ("message", string(error.to_string())),
    ];
    let path = match error {
        RuntimeError::Io { path, .. } => Some(path.as_path()),
        _ => path,
    };
    if let Some(path) = path {
        fields.insert(0, ("file", string(path.display().to_string())));
    }
    object(language, fields)
}

fn parse_error(
    error: &RuntimeParseError,
    source: Option<&crate::run::run_source::RunSource>,
    language: OutputLanguage,
) -> JsonValue {
    let mut fields = vec![
        ("file", string(error.path.to_string())),
        ("line", JsonValue::Number(error.line as f64)),
        ("phase", string("parse")),
        ("message", string(&error.message)),
    ];
    let line = error
        .source
        .as_ref()
        .map(|source| source.text.as_str())
        .or_else(|| source.and_then(|source| source.line(error.line)));
    if let Some(line) = line {
        fields.push(("source", string(line)));
    }
    if let Some(column) = error.source.as_ref().and_then(|source| source.column) {
        fields.push(("column", JsonValue::Number(column as f64)));
    }
    object(language, fields)
}
