use crate::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

const HARNESS_NAME: &str = "litex-agent-harness";
const HARNESS_VERSION: &str = "0.1";
const MAIN_DOT_LIT: &str = "main.lit";

pub fn run_harness_for_code(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_harness_on_source("code", label, code, hide_file_paths)
}

pub fn run_harness_for_file(file_path: &str, hide_file_paths: bool) -> (bool, String) {
    let resolved_path = match resolve_litex_file_path(file_path) {
        Ok(path) => path,
        Err(message) => {
            return harness_target_error_output("file", file_path, hide_file_paths, message);
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
            return harness_target_error_output(
                "file",
                resolved_path.as_str(),
                hide_file_paths,
                message,
            );
        }
    };

    run_harness_on_source(
        "file",
        resolved_path.as_str(),
        source_code.as_str(),
        hide_file_paths,
    )
}

pub fn run_harness_for_repo(repo_path: &str, hide_file_paths: bool) -> (bool, String) {
    let joined = Path::new(repo_path).join(MAIN_DOT_LIT);
    let joined_string = match joined.to_str() {
        Some(path_string) => path_string.to_string(),
        None => {
            return harness_target_error_output(
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
            return harness_target_error_output("repo", repo_path, hide_file_paths, message);
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
            return harness_target_error_output("repo", repo_path, hide_file_paths, message);
        }
    };

    run_harness_on_source(
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

fn run_harness_on_source(
    target_kind: &str,
    target_label: &str,
    source_code: &str,
    hide_file_paths: bool,
) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(target_label);
    runtime.module_manager.hide_file_paths_in_output = hide_file_paths;

    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    let (trace_succeeded, trace_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);

    let proof_debt_count = count_know_statements(stmt_results.as_slice());
    let ok = trace_succeeded && proof_debt_count == 0;
    let result_label = if ok { "success" } else { "error" };
    let next_action = next_action_for_run(runtime_error.as_ref(), proof_debt_count);

    let fields = vec![
        (
            "harness".to_string(),
            JsonValue::JsonString(HARNESS_NAME.to_string()),
        ),
        (
            "harness_version".to_string(),
            JsonValue::JsonString(HARNESS_VERSION.to_string()),
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
        (
            "summary".to_string(),
            summary_json_value(
                stmt_results.as_slice(),
                proof_debt_count,
                runtime_error.as_ref(),
            ),
        ),
        (
            "next_action".to_string(),
            JsonValue::JsonString(next_action.to_string()),
        ),
        (
            "failure".to_string(),
            failure_json_value(runtime_error.as_ref(), hide_file_paths),
        ),
        (
            "trace".to_string(),
            JsonValue::JsonString(trace_output.trim().to_string()),
        ),
    ];

    (ok, render_json_value(&JsonValue::Object(fields), 0))
}

fn harness_target_error_output(
    target_kind: &str,
    target_label: &str,
    hide_file_paths: bool,
    message: String,
) -> (bool, String) {
    let failure = JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("target_error".to_string()),
        ),
        (
            "error_type".to_string(),
            JsonValue::JsonString("TargetError".to_string()),
        ),
        ("line".to_string(), JsonValue::Null),
        ("message".to_string(), JsonValue::JsonString(message)),
    ]);
    let output = JsonValue::Object(vec![
        (
            "harness".to_string(),
            JsonValue::JsonString(HARNESS_NAME.to_string()),
        ),
        (
            "harness_version".to_string(),
            JsonValue::JsonString(HARNESS_VERSION.to_string()),
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
        (
            "summary".to_string(),
            JsonValue::Object(vec![
                ("checked_statements".to_string(), JsonValue::Number(0)),
                ("successful_statements".to_string(), JsonValue::Number(0)),
                (
                    "proof_debt_know_statements".to_string(),
                    JsonValue::Number(0),
                ),
                ("error_count".to_string(), JsonValue::Number(1)),
            ]),
        ),
        (
            "next_action".to_string(),
            JsonValue::JsonString("fix_target".to_string()),
        ),
        ("failure".to_string(), failure),
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

fn summary_json_value(
    stmt_results: &[StmtResult],
    proof_debt_count: usize,
    runtime_error: Option<&RuntimeError>,
) -> JsonValue {
    let successful_count = stmt_results
        .iter()
        .filter(|result| result.is_true())
        .count();
    let error_count = if runtime_error.is_some() { 1 } else { 0 };
    JsonValue::Object(vec![
        (
            "checked_statements".to_string(),
            JsonValue::Number(stmt_results.len()),
        ),
        (
            "successful_statements".to_string(),
            JsonValue::Number(successful_count),
        ),
        (
            "proof_debt_know_statements".to_string(),
            JsonValue::Number(proof_debt_count),
        ),
        ("error_count".to_string(), JsonValue::Number(error_count)),
    ])
}

fn failure_json_value(runtime_error: Option<&RuntimeError>, hide_file_paths: bool) -> JsonValue {
    match runtime_error {
        Some(error) => runtime_error_feedback_json_value(error, hide_file_paths),
        None => JsonValue::Null,
    }
}

fn runtime_error_feedback_json_value(error: &RuntimeError, hide_file_paths: bool) -> JsonValue {
    let root_cause = deepest_error(error);
    JsonValue::Object(vec![
        (
            "kind".to_string(),
            JsonValue::JsonString("verifier_error".to_string()),
        ),
        (
            "error_type".to_string(),
            JsonValue::JsonString(error.display_label().to_string()),
        ),
        ("line".to_string(), line_json_value(&error.line_file())),
        (
            "message".to_string(),
            JsonValue::JsonString(error_feedback_message(error)),
        ),
        (
            "statement".to_string(),
            statement_json_value(error_statement(error)),
        ),
        (
            "root_cause".to_string(),
            root_cause_json_value(root_cause, hide_file_paths),
        ),
        (
            "error_chain".to_string(),
            JsonValue::Array(error_chain_json_values(error, hide_file_paths)),
        ),
    ])
}

fn root_cause_json_value(error: &RuntimeError, hide_file_paths: bool) -> JsonValue {
    let line_file = error.line_file();
    let mut fields = vec![
        (
            "error_type".to_string(),
            JsonValue::JsonString(error.display_label().to_string()),
        ),
        ("line".to_string(), line_json_value(&line_file)),
    ];
    if !hide_file_paths {
        fields.push(("source".to_string(), source_json_value(&line_file)));
    }
    fields.push((
        "message".to_string(),
        JsonValue::JsonString(error_feedback_message(error)),
    ));
    fields.push((
        "statement".to_string(),
        statement_json_value(error_statement(error)),
    ));
    JsonValue::Object(fields)
}

fn error_chain_json_values(error: &RuntimeError, hide_file_paths: bool) -> Vec<JsonValue> {
    let mut values: Vec<JsonValue> = Vec::new();
    let mut current = Some(error);
    while let Some(current_error) = current {
        values.push(root_cause_json_value(current_error, hide_file_paths));
        current = previous_error(current_error);
    }
    values
}

fn statement_json_value(stmt: Option<&Stmt>) -> JsonValue {
    match stmt {
        Some(stmt) => JsonValue::Object(vec![
            (
                "type".to_string(),
                JsonValue::JsonString(stmt.stmt_type_name()),
            ),
            ("text".to_string(), JsonValue::JsonString(stmt.to_string())),
        ]),
        None => JsonValue::Null,
    }
}

fn line_json_value(line_file: &LineFile) -> JsonValue {
    if line_file_is_default(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

fn source_json_value(line_file: &LineFile) -> JsonValue {
    if line_file_is_default(line_file) {
        JsonValue::Null
    } else {
        JsonValue::JsonString(line_file.1.as_ref().to_string())
    }
}

fn line_file_is_default(line_file: &LineFile) -> bool {
    line_file.0 == 0 && line_file.1.is_empty()
}

fn count_know_statements(stmt_results: &[StmtResult]) -> usize {
    let mut count = 0;
    for result in stmt_results {
        if let StmtResult::NonFactualStmtSuccess(success) = result {
            if let Stmt::KnowStmt(_) = &success.stmt {
                count += 1;
            }
            count += count_know_statements(success.inside_results.as_slice());
        }
    }
    count
}

fn next_action_for_run(
    runtime_error: Option<&RuntimeError>,
    proof_debt_count: usize,
) -> &'static str {
    if let Some(error) = runtime_error {
        if error_chain_contains_label(error, "UnknownError") {
            return "add_intermediate_fact";
        }
        return match error {
            RuntimeError::ParseError(_)
            | RuntimeError::WellDefinedError(_)
            | RuntimeError::DefineParamsError(_)
            | RuntimeError::NameAlreadyUsedError(_)
            | RuntimeError::InstantiateError(_)
            | RuntimeError::ArithmeticError(_) => "fix_error",
            RuntimeError::VerifyError(_) => "split_goal_or_add_fact",
            RuntimeError::ExecStmtError(_) => "inspect_nested_error",
            RuntimeError::NewFactError(_)
            | RuntimeError::StoreFactError(_)
            | RuntimeError::InferError(_)
            | RuntimeError::UnknownError(_) => "inspect_error",
        };
    }
    if proof_debt_count > 0 {
        return "reduce_proof_debt";
    }
    "done"
}

fn error_chain_contains_label(error: &RuntimeError, label: &str) -> bool {
    let mut current = Some(error);
    while let Some(current_error) = current {
        if current_error.display_label() == label {
            return true;
        }
        current = previous_error(current_error);
    }
    false
}

fn deepest_error<'a>(error: &'a RuntimeError) -> &'a RuntimeError {
    let mut current = error;
    while let Some(previous) = previous_error(current) {
        current = previous;
    }
    current
}

fn previous_error<'a>(error: &'a RuntimeError) -> Option<&'a RuntimeError> {
    match error {
        RuntimeError::ArithmeticError(e)
        | RuntimeError::NewFactError(e)
        | RuntimeError::StoreFactError(e)
        | RuntimeError::ParseError(e)
        | RuntimeError::ExecStmtError(e)
        | RuntimeError::WellDefinedError(e)
        | RuntimeError::VerifyError(e)
        | RuntimeError::UnknownError(e)
        | RuntimeError::InferError(e)
        | RuntimeError::NameAlreadyUsedError(e)
        | RuntimeError::DefineParamsError(e)
        | RuntimeError::InstantiateError(e) => e.previous_error.as_deref(),
    }
}

fn error_message(error: &RuntimeError) -> &str {
    match error {
        RuntimeError::ArithmeticError(e)
        | RuntimeError::NewFactError(e)
        | RuntimeError::StoreFactError(e)
        | RuntimeError::ParseError(e)
        | RuntimeError::ExecStmtError(e)
        | RuntimeError::WellDefinedError(e)
        | RuntimeError::VerifyError(e)
        | RuntimeError::UnknownError(e)
        | RuntimeError::InferError(e)
        | RuntimeError::NameAlreadyUsedError(e)
        | RuntimeError::DefineParamsError(e)
        | RuntimeError::InstantiateError(e) => e.msg.as_str(),
    }
}

fn error_feedback_message(error: &RuntimeError) -> String {
    let message = error_message(error);
    if !message.trim().is_empty() {
        return message.to_string();
    }
    if let Some(stmt) = error_statement(error) {
        return stmt.to_string();
    }
    error.display_label().to_string()
}

fn error_statement(error: &RuntimeError) -> Option<&Stmt> {
    match error {
        RuntimeError::ArithmeticError(e)
        | RuntimeError::NewFactError(e)
        | RuntimeError::StoreFactError(e)
        | RuntimeError::ParseError(e)
        | RuntimeError::ExecStmtError(e)
        | RuntimeError::WellDefinedError(e)
        | RuntimeError::VerifyError(e)
        | RuntimeError::UnknownError(e)
        | RuntimeError::InferError(e)
        | RuntimeError::NameAlreadyUsedError(e)
        | RuntimeError::DefineParamsError(e)
        | RuntimeError::InstantiateError(e) => e.statement.as_ref(),
    }
}

fn remove_windows_carriage_return(text: &str) -> String {
    text.replace('\r', "")
}
