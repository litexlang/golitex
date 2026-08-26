use crate::prelude::*;

const RUNNER_NAME: &str = "litex-runner";
const RUNNER_VERSION: &str = "0.1";

pub struct RunnerRequest {
    pub run: RunRequest,
    pub hide_file_paths: bool,
}

impl RunnerRequest {
    pub fn new(run: RunRequest, hide_file_paths: bool) -> Self {
        Self {
            run,
            hide_file_paths,
        }
    }
}

pub fn run_runner(request: RunnerRequest) -> (bool, String) {
    let RunnerRequest {
        run: run_request,
        hide_file_paths,
    } = request;
    let outcome = run(run_request);
    if let Some(message) = outcome.target_error {
        return runner_target_error_output(
            outcome.target_kind,
            outcome.target_path.as_deref(),
            hide_file_paths,
            message,
        );
    }
    runner_output_from_trace(
        outcome.target_kind,
        outcome.target_path.as_deref(),
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
            target_json_value(target_kind, target_path, hide_file_paths),
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
            target_json_value(target_kind, target_path, hide_file_paths),
        ),
        ("error".to_string(), error),
        ("trace".to_string(), JsonValue::JsonString(String::new())),
    ];
    (false, render_runner_json_value(JsonValue::Object(fields)))
}

fn render_runner_json_value(value: JsonValue) -> String {
    render_json_value(&value, 0)
}

fn target_json_value(
    target_kind: RunTargetKind,
    target_path: Option<&str>,
    hide_file_paths: bool,
) -> JsonValue {
    let label = if target_kind == RunTargetKind::Code {
        "-runner -e".to_string()
    } else if hide_file_paths {
        "entry".to_string()
    } else {
        target_path.unwrap_or("entry").to_string()
    };

    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target_kind.json_name().to_string()),
        ),
        ("label".to_string(), JsonValue::JsonString(label)),
    ])
}

#[cfg(test)]
#[path = "../../tests/unit/runner/target_execution/tests.rs"]
mod tests;
