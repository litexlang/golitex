use crate::prelude::*;

pub(super) fn render_cli_error(message: &str) -> String {
    render_json_value(
        &JsonValue::Object(vec![
            string_field("kind", "cli_error"),
            ("ok".to_string(), JsonValue::Bool(false)),
            string_field("message", message),
        ]),
        0,
    )
}

pub(super) fn render_version(version: &str) -> String {
    render_json_value(
        &JsonValue::Object(vec![
            string_field("kind", "version"),
            ("ok".to_string(), JsonValue::Bool(true)),
            string_field("version", version),
        ]),
        0,
    )
}

pub(super) fn render_run(outcome: &RunOutcome, input_path: Option<&str>) -> String {
    let target = run_target_kind(&outcome.target).0;
    let statement_results = outcome
        .stmt_results
        .iter()
        .map(|result| JsonValue::RawJson(render_statement_result_json(result)))
        .collect::<Vec<_>>();
    let error = if let Some(message) = outcome.target_error.as_deref() {
        simple_error("target_error", message)
    } else if let Some(error) = outcome.runtime_error.as_ref() {
        JsonValue::RawJson(render_runtime_error_json(&outcome.runtime, error, true))
    } else {
        JsonValue::Null
    };
    let fields = vec![
        string_field("kind", "run"),
        ("ok".to_string(), JsonValue::Bool(outcome.ok)),
        string_field("target", target),
        (
            "path".to_string(),
            input_path
                .map(|path| JsonValue::JsonString(path.to_string()))
                .unwrap_or(JsonValue::Null),
        ),
        (
            "statement_results".to_string(),
            JsonValue::Array(statement_results),
        ),
        ("error".to_string(), error),
    ];
    strip_free_param_numeric_tags_in_display(&render_json_value(&JsonValue::Object(fields), 0))
}

pub(super) fn render_artifact(
    artifact: &str,
    format: &str,
    target: &str,
    path: Option<&str>,
    output_path: Option<&str>,
    content: JsonValue,
    error: JsonValue,
) -> String {
    let ok = matches!(error, JsonValue::Null);
    render_json_value(
        &JsonValue::Object(vec![
            string_field("kind", "artifact"),
            ("ok".to_string(), JsonValue::Bool(ok)),
            string_field("artifact", artifact),
            string_field("format", format),
            string_field("target", target),
            ("path".to_string(), optional_string(path)),
            ("output_path".to_string(), optional_string(output_path)),
            ("content".to_string(), content),
            ("error".to_string(), error),
        ]),
        0,
    )
}

pub(super) fn simple_error(kind: &str, message: &str) -> JsonValue {
    JsonValue::Object(vec![
        string_field("kind", kind),
        string_field("message", message),
    ])
}

pub(super) fn run_target_kind(target: &RunTarget) -> (&'static str, bool) {
    match target {
        RunTarget::Eval => ("eval", false),
        RunTarget::File { .. } | RunTarget::IsolatedFile { .. } => ("file", true),
        RunTarget::Repository { .. } => ("repository", true),
    }
}

pub(super) fn execution_target(execution: LitexExecution) -> (&'static str, bool) {
    match execution {
        LitexExecution::Eval => ("eval", false),
        LitexExecution::File | LitexExecution::IsolatedFile => ("file", true),
        LitexExecution::Repository => ("repository", true),
        LitexExecution::Repl => ("repl", false),
        LitexExecution::Session | LitexExecution::IsolatedSession => ("session", false),
    }
}

fn string_field(key: &str, value: &str) -> (String, JsonValue) {
    (key.to_string(), JsonValue::JsonString(value.to_string()))
}

fn optional_string(value: Option<&str>) -> JsonValue {
    value
        .map(|value| JsonValue::JsonString(value.to_string()))
        .unwrap_or(JsonValue::Null)
}
