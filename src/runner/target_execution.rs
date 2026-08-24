use crate::prelude::*;

const RUNNER_NAME: &str = "litex-runner";
const RUNNER_VERSION: &str = "0.1";

pub fn run_runner_for_code_strict(
    code: &str,
    label: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    run_runner_for_code_strict_with_language(code, label, hide_file_paths, OutputLanguage::English)
}

pub fn run_runner_for_code_strict_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_runner_on_source("code", label, code, hide_file_paths, true, output_language)
}

pub fn run_runner_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_runner_for_file_with_strict(file_path, hide_file_paths, false)
}

pub fn run_runner_for_file_with_strict(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_runner_for_file_with_strict_and_language(
        file_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_runner_for_file_with_strict_and_language(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_runner_for_file_with_strict_language_and_isolation(
        file_path,
        hide_file_paths,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_runner_for_file_with_strict_language_and_isolation(
    file_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> (bool, String) {
    let resolved_path = match resolve_source_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return runner_target_error_output("file", file_path, hide_file_paths, message);
        }
    };

    let mut runtime = Runtime::new();
    runtime.set_output_style(if hide_file_paths {
        OutputStyle::Normal
    } else {
        OutputStyle::Detailed
    });
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let (stmt_results, runtime_error) = crate::pipeline::run_file_with_project_context(
        resolved_path.as_str(),
        &mut runtime,
        force_isolated,
    );
    let (ok, trace_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    runner_output_from_trace(
        "file",
        resolved_path.as_str(),
        hide_file_paths,
        ok,
        trace_output,
    )
}

pub fn run_runner_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    run_runner_for_repo_with_strict(repo_path, hide_file_paths, false)
}

pub fn run_runner_for_repo_with_strict(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
) -> (bool, String) {
    run_runner_for_repo_with_strict_and_language(
        repo_path,
        hide_file_paths,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_runner_for_repo_with_strict_and_language(
    repo_path: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    let (ok, trace_output) = run_repository_with_output(
        repo_path,
        !hide_file_paths,
        strict_mode,
        output_language,
        false,
    );
    runner_output_from_trace("repo", repo_path, hide_file_paths, ok, trace_output)
}

pub fn run_runner_on_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    hide_file_paths: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new();
    runtime.start_isolated_source(target_label);
    runtime.set_output_style(if hide_file_paths {
        OutputStyle::Normal
    } else {
        OutputStyle::Detailed
    });
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;

    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let (ok, trace_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    runner_output_from_trace(target_kind, target_label, hide_file_paths, ok, trace_output)
}

fn runner_output_from_trace(
    target_kind: &str,
    target_label: &str,
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
            target_json_value(target_kind, target_label, hide_file_paths),
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
    target_kind: &str,
    target_label: &str,
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
    let output = JsonValue::Object(vec![
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
            target_json_value(target_kind, target_label, hide_file_paths),
        ),
        ("error".to_string(), error),
        ("trace".to_string(), JsonValue::JsonString(String::new())),
    ]);

    (false, render_runner_json_value(output))
}

fn render_runner_json_value(value: JsonValue) -> String {
    // Runner JSON is a machine interface. JSON v2 keeps structural keys and
    // enum names language-neutral; only human-readable diagnostic messages may
    // still be localized before they enter this envelope.
    render_json_value(&value, 0)
}

fn target_json_value(target_kind: &str, target_label: &str, hide_file_paths: bool) -> JsonValue {
    let label = if hide_file_paths && target_kind != "code" {
        "entry".to_string()
    } else {
        target_label.to_string()
    };

    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString(target_kind.to_string()),
        ),
        ("label".to_string(), JsonValue::JsonString(label)),
    ])
}

#[cfg(test)]
#[path = "../../tests/unit/runner/target_execution/tests.rs"]
mod tests;
