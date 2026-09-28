use crate::prelude::*;

const RUNNER_NAME: &str = "litex-runner";
const RUNNER_VERSION: &str = "0.2";

pub fn render_runner(outcome: RunOutcome, hide_file_paths: bool) -> (bool, String) {
    let target_kind = outcome.target.kind();
    let target_path = outcome.target.path();
    if let Some(message) = outcome.target_error {
        return runner_target_error_output(target_kind, target_path, hide_file_paths, message);
    }
    runner_output_from_trace(
        target_kind,
        target_path,
        hide_file_paths,
        outcome.ok,
        outcome.output,
    )
}

fn runner_output_from_trace(
    target_kind: RunTargetKind,
    target_path: Option<&str>,
    hide_file_paths: bool,
    ok: bool,
    trace_output: String,
) -> (bool, String) {
    let result_label = if ok { "success" } else { "error" };

    let fields = vec![
        (
            "runner".to_string(),
            JsonValue::JsonString(RUNNER_NAME.to_string()),
        ),
        (
            "runner_version".to_string(),
            JsonValue::JsonString(RUNNER_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString(result_label.to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(ok)),
        (
            "target".to_string(),
            run_target_json_value(target_kind.json_name(), target_path, hide_file_paths),
        ),
        ("error".to_string(), JsonValue::Null),
        (
            "trace".to_string(),
            JsonValue::JsonString(trace_output.trim().to_string()),
        ),
    ];
    (ok, render_runner_json_value(JsonValue::Object(fields)))
}

fn runner_target_error_output(
    target_kind: RunTargetKind,
    target_path: Option<&str>,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let error = JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("target_error".to_string()),
        ),
        ("message".to_string(), JsonValue::JsonString(message)),
    ]);
    let fields = vec![
        (
            "runner".to_string(),
            JsonValue::JsonString(RUNNER_NAME.to_string()),
        ),
        (
            "runner_version".to_string(),
            JsonValue::JsonString(RUNNER_VERSION.to_string()),
        ),
        (
            "result".to_string(),
            JsonValue::JsonString("error".to_string()),
        ),
        ("ok".to_string(), JsonValue::Bool(false)),
        (
            "target".to_string(),
            run_target_json_value(target_kind.json_name(), target_path, hide_file_paths),
        ),
        ("error".to_string(), error),
        ("trace".to_string(), JsonValue::JsonString(String::new())),
    ];
    (false, render_runner_json_value(JsonValue::Object(fields)))
}

fn render_runner_json_value(value: JsonValue) -> String {
    render_json_value(&value, 0)
}

#[cfg(test)]
#[path = "../../tests/unit/runner/target_execution/tests.rs"]
mod tests;
