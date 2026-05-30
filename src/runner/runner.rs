use crate::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

const RUNNER_NAME: &str = "litex-runner";
const RUNNER_VERSION: &str = "0.1";
const MAIN_DOT_LIT: &str = "main.lit";

pub fn run_runner_for_code(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_runner_on_source("code", label, code, hide_file_paths)
}

pub fn run_runner_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    let resolved_path = match resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return runner_target_error_output("file", file_path, hide_file_paths, message);
        }
    };

    let source_code = match fs::read_to_string(resolved_path.as_str()) {
        Ok(content) => content,
        Err(error) => {
            let message = if hide_file_paths {
                format!("could not read entry file: {}", error)
            } else {
                format!("could not read file {:?}: {}", resolved_path, error)
            };
            return runner_target_error_output(
                "file",
                resolved_path.as_str(),
                hide_file_paths,
                message,
            );
        }
    };

    run_runner_on_source(
        "file",
        resolved_path.as_str(),
        source_code.as_str(),
        hide_file_paths,
    )
}

pub fn run_runner_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    let joined = Path::new(repo_path).join(MAIN_DOT_LIT);
    let joined_string = match joined.to_str() {
        Some(path_string) => path_string.to_string(),
        None => {
            return runner_target_error_output(
                "repo",
                repo_path,
                hide_file_paths,
                "repo path is not valid UTF-8".to_string(),
            );
        }
    };

    let resolved_path = match resolve_litex_file_path(joined_string.as_str()) {
        Ok(path) => path,
        Err(message) => {
            return runner_target_error_output("repo", repo_path, hide_file_paths, message);
        }
    };

    let source_code = match fs::read_to_string(resolved_path.as_str()) {
        Ok(content) => content,
        Err(error) => {
            let message = if hide_file_paths {
                format!("could not read entry file: {}", error)
            } else {
                format!(
                    "could not read repo main file {:?}: {}",
                    resolved_path, error
                )
            };
            return runner_target_error_output("repo", repo_path, hide_file_paths, message);
        }
    };

    run_runner_on_source(
        "repo",
        resolved_path.as_str(),
        source_code.as_str(),
        hide_file_paths,
    )
}

pub fn resolve_litex_file_path(file_path: &str) -> Result<String, String> {
    let path = remove_windows_carriage_return(file_path);
    let abs_file_path: PathBuf = if Path::new(path.as_str()).is_absolute() {
        PathBuf::from(path.as_str())
    } else {
        let working_directory = env::current_dir()
            .map_err(|error| format!("failed to get current working directory: {}", error))?;
        working_directory.join(path.as_str())
    };

    if abs_file_path.parent().is_none() {
        return Err("could not get parent directory of file path".to_string());
    }

    match abs_file_path.to_str() {
        Some(path_string) => Ok(path_string.to_string()),
        None => Err("file path is not valid UTF-8".to_string()),
    }
}

fn run_runner_on_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(target_label);
    runtime.detail_output = !hide_file_paths;
    runtime.module_manager.borrow_mut().hide_file_paths_in_output = hide_file_paths;

    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let (ok, trace_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
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

    (ok, render_json_value(&JsonValue::Object(fields), 0))
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

    (false, render_json_value(&output, 0))
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

fn remove_windows_carriage_return(text: &str) -> String {
    text.replace('\r', "")
}
