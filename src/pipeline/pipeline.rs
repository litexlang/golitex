use crate::common::json_value::{render_json_value, JsonValue};
use crate::pipeline::display::{display_runtime_error_json, display_stmt_exec_result_json};
use crate::pipeline::summary::display_run_summary_json_with_runtime;
use crate::pipeline::{run_repository_file_target, run_stmt_at_global_env};
use crate::prelude::*;
use std::fs;
use std::path::Path;
use std::rc::Rc;
use std::time::Instant;

pub use crate::result::StmtResult;

pub fn run_source_code_in_file(entry_file_path: &str) -> String {
    run_file_with_output_style(
        entry_file_path,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        false,
    )
    .1
}

pub fn run_source_code_in_file_for_cli(entry_file_path: &str, detail_output: bool) -> String {
    run_source_code_in_file_for_cli_with_strict(entry_file_path, detail_output, false)
}

pub fn run_source_code_in_file_for_cli_with_strict(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
) -> String {
    run_source_code_in_file_for_cli_with_strict_and_language(
        entry_file_path,
        detail_output,
        strict_mode,
        OutputLanguage::English,
    )
}

pub fn run_source_code_in_file_for_cli_with_strict_and_language(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
) -> String {
    run_source_code_in_file_for_cli_with_summary_and_language(
        entry_file_path,
        detail_output,
        strict_mode,
        output_language,
        false,
    )
}

pub fn run_source_code_in_file_for_cli_with_summary_and_language(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    run_file_with_output_style(
        entry_file_path,
        output_style_from_detail_output(detail_output),
        strict_mode,
        output_language,
        summarize,
        false,
    )
    .1
}

pub fn run_source_code_in_file_for_cli_with_summary_and_language_and_isolation(
    entry_file_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
    force_isolated: bool,
) -> String {
    run_file_with_output_style(
        entry_file_path,
        output_style_from_detail_output(detail_output),
        strict_mode,
        output_language,
        summarize,
        force_isolated,
    )
    .1
}

pub fn run_source_code_in_file_for_cli_with_output_style_and_summary_and_language_and_isolation(
    entry_file_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
    force_isolated: bool,
) -> String {
    run_file_with_output_style(
        entry_file_path,
        output_style,
        strict_mode,
        output_language,
        summarize,
        force_isolated,
    )
    .1
}

pub fn run_source_code_in_file_with_ok(entry_file_path: &str) -> (bool, String) {
    run_file_with_output_style(
        entry_file_path,
        OutputStyle::Normal,
        false,
        OutputLanguage::English,
        false,
        false,
    )
}

pub fn run_source_code_in_repository_for_cli_with_summary_and_language(
    repository_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    run_repository_with_output_style(
        repository_path,
        output_style_from_detail_output(detail_output),
        strict_mode,
        output_language,
        summarize,
    )
    .1
}

pub fn run_source_code_in_repository_for_cli_with_output_style_and_summary_and_language(
    repository_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    run_repository_with_output_style(
        repository_path,
        output_style,
        strict_mode,
        output_language,
        summarize,
    )
    .1
}

pub fn run_repository_with_output(
    repository_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    run_repository_with_output_style(
        repository_path,
        output_style_from_detail_output(detail_output),
        strict_mode,
        output_language,
        summarize,
    )
}

pub fn run_repository_with_output_style(
    repository_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.isolated = false;
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let target = match discover_repository(&mut runtime, repository_path) {
        Ok(target) => target,
        Err(error) => {
            return render_run_source_code_output(&runtime, &vec![], &Some(error), true);
        }
    };
    let (stmt_results, runtime_error) = run_repository_file_target(&mut runtime, target);
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if summarize {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    (ok, output)
}

fn run_file_with_output_style(
    entry_file_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
    force_isolated: bool,
) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let (stmt_results, runtime_error) =
        run_file_with_project_context(entry_file_path, &mut runtime, force_isolated);
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if summarize {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    (ok, output)
}

fn output_style_from_detail_output(detail_output: bool) -> OutputStyle {
    if detail_output {
        OutputStyle::Detailed
    } else {
        OutputStyle::Normal
    }
}

pub fn run_file_with_project_context(
    entry_file_path: &str,
    runtime: &mut Runtime,
    force_isolated: bool,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    run_file_with_project_context_and_trusted_prefix(entry_file_path, runtime, force_isolated, None)
}

pub fn run_file_with_project_context_and_trusted_prefix(
    entry_file_path: &str,
    runtime: &mut Runtime,
    force_isolated: bool,
    trust_before_line: Option<usize>,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    runtime.isolated = false;
    runtime.clear_trusted_prefix_execution_policy();
    runtime.trusted_prefix_report = None;
    runtime.trusted_prefix_setup_error = None;
    let path = Path::new(entry_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                entry_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
        );
    }
    if let Some(before_line) = trust_before_line {
        let source_code = match fs::read_to_string(entry_file_path) {
            Ok(content) => content,
            Err(error) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        format!("could not read file: {}", error).as_str(),
                    )),
                )
            }
        };
        let source_code = remove_windows_carriage_return(source_code.as_str());
        let blocks =
            match Tokenizer::new().parse_blocks(source_code.as_str(), Rc::from(entry_file_path)) {
                Ok(blocks) => blocks,
                Err(error) => return (vec![], Some(error)),
            };
        let statement_lines = blocks
            .iter()
            .map(|block| block.line_file.0)
            .collect::<Vec<_>>();
        if !statement_lines.contains(&before_line) {
            let message = trusted_prefix_boundary_error_message(
                entry_file_path,
                before_line,
                &statement_lines,
            );
            runtime.trusted_prefix_setup_error = Some(message.clone());
            return (
                vec![],
                Some(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        message,
                        (before_line, Rc::from(entry_file_path)),
                    ))
                    .into(),
                ),
            );
        }
        let trusted_top_level_statements = statement_lines
            .iter()
            .filter(|line| **line < before_line)
            .count();
        runtime.trusted_prefix_report = Some(TrustedPrefixReport::new(
            entry_file_path.to_string(),
            before_line,
            trusted_top_level_statements,
            before_line,
        ));
    }
    if !force_isolated {
        match discover_repository_for_file(runtime, entry_file_path) {
            Ok(Some(target)) => {
                if let Some(before_line) = trust_before_line {
                    let (module_id, layer) = match target {
                        RepositoryFileTarget::Module(module_id) => {
                            (module_id, ExecutionLayer::Main)
                        }
                        RepositoryFileTarget::File { module_id, file_id } => {
                            (module_id, ExecutionLayer::File(file_id))
                        }
                    };
                    runtime.configure_trusted_prefix(module_id, layer, before_line);
                }
                let result = run_repository_file_target(runtime, target);
                runtime.clear_trusted_prefix_execution_policy();
                return result;
            }
            Ok(None) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        "litex -f requires a litex.config in the same folder; use `litex -isolated -f <file>` for an isolated file",
                    )),
                )
            }
            Err(error) => return (vec![], Some(error)),
        }
    }

    runtime.isolated = true;

    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(error) => {
            return (
                vec![],
                Some(file_target_error(
                    entry_file_path,
                    format!("could not read file: {}", error).as_str(),
                )),
            )
        }
    };
    runtime.new_file_path_new_env_new_name_scope(entry_file_path);
    if let Some(before_line) = trust_before_line {
        runtime.configure_trusted_prefix(
            runtime.current_module_id(),
            ExecutionLayer::Main,
            before_line,
        );
    }
    let result = run_source_code(
        remove_windows_carriage_return(source_code.as_str()).as_str(),
        runtime,
    );
    runtime.clear_trusted_prefix_execution_policy();
    result
}

fn file_target_error(entry_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(entry_file_path)),
    ))
    .into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RunSourceFailureKind {
    TryStmt,
    Other,
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let (stmt_results, runtime_error, _) = run_source_code_with_failure_kind(source_code, runtime);
    (stmt_results, runtime_error)
}

pub(crate) fn run_source_code_with_failure_kind(
    source_code: &str,
    runtime: &mut Runtime,
) -> (
    Vec<StmtResult>,
    Option<RuntimeError>,
    Option<RunSourceFailureKind>,
) {
    if !runtime.has_active_execution_frame() {
        return (
            vec![],
            Some(
                ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                    "runtime has no active source context; initialize a file or repository before running source"
                        .to_string(),
                ))
                .into(),
            ),
            Some(RunSourceFailureKind::Other),
        );
    }

    let tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let source_starts_with_try = source_code
        .lines()
        .find(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .is_some_and(|line| line.trim_end() == "try:");
    let blocks = match tokenizer.parse_blocks(source_code, current_file_path) {
        Ok(b) => b,
        Err(e) => {
            let failure_kind = if source_starts_with_try {
                RunSourceFailureKind::TryStmt
            } else {
                RunSourceFailureKind::Other
            };
            return (vec![], Some(e), Some(failure_kind));
        }
    };
    let trust_before_line = runtime.trusted_prefix_before_line_for_current_target();
    if let Some(before_line) = trust_before_line {
        let statement_lines = blocks
            .iter()
            .map(|block| block.line_file.0)
            .collect::<Vec<_>>();
        if !statement_lines.contains(&before_line) {
            let message = trusted_prefix_boundary_error_message(
                runtime.current_file_path_rc().as_ref(),
                before_line,
                &statement_lines,
            );
            runtime.trusted_prefix_setup_error = Some(message.clone());
            return (
                vec![],
                Some(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        message,
                        (before_line, runtime.current_file_path_rc()),
                    ))
                    .into(),
                ),
                Some(RunSourceFailureKind::Other),
            );
        }
        let trusted_top_level_statements = statement_lines
            .iter()
            .filter(|line| **line < before_line)
            .count();
        runtime.trusted_prefix_report = Some(TrustedPrefixReport::new(
            runtime.current_file_path_rc().to_string(),
            before_line,
            trusted_top_level_statements,
            before_line,
        ));
    }

    let profile_repository_run = std::env::var_os("LITEX_PROFILE_REPOSITORY").is_some();
    let mut stmt_results: Vec<StmtResult> = Vec::new();
    for mut block in blocks {
        let statement_start = profile_repository_run.then(Instant::now);
        let parsing_try_stmt = block.current_token_is_equal_to(TRY);
        let stmt: Stmt = {
            match runtime.parse_stmt(&mut block) {
                Ok(s) => s,
                Err(e) => {
                    let failure_kind = if parsing_try_stmt {
                        RunSourceFailureKind::TryStmt
                    } else {
                        RunSourceFailureKind::Other
                    };
                    return (stmt_results, Some(e), Some(failure_kind));
                }
            }
        };
        let executing_try_stmt = matches!(&stmt, Stmt::ProofBlock(ProofBlockStmt::TryStmt(_)));
        let trusted_prefix_statement =
            trust_before_line.is_some_and(|before_line| stmt.line_file().0 < before_line);
        if trust_before_line.is_some() {
            runtime.begin_trusted_prefix_statement(trusted_prefix_statement);
        }
        let previous_execution_mode = trusted_prefix_statement
            .then(|| runtime.replace_current_execution_mode(ExecutionMode::Trusted));
        let result = match run_stmt_at_global_env(&stmt, runtime) {
            Ok(r) => r,
            Err(e) => {
                if let Some(previous_execution_mode) = previous_execution_mode {
                    runtime.replace_current_execution_mode(previous_execution_mode);
                }
                runtime.end_trusted_prefix_statement();
                let failure_kind = if executing_try_stmt {
                    RunSourceFailureKind::TryStmt
                } else {
                    RunSourceFailureKind::Other
                };
                return (stmt_results, Some(e), Some(failure_kind));
            }
        };
        if let Some(previous_execution_mode) = previous_execution_mode {
            runtime.replace_current_execution_mode(previous_execution_mode);
        }
        runtime.end_trusted_prefix_statement();
        if let Some(statement_start) = statement_start {
            let line_file = stmt.line_file();
            eprintln!(
                "repository statement {}:{}: {:.2} ms",
                line_file.1,
                line_file.0,
                statement_start.elapsed().as_secs_f64() * 1000.0,
            );
        }
        stmt_results.push(result);
    }

    (stmt_results, None, None)
}

fn trusted_prefix_boundary_error_message(
    file: &str,
    before_line: usize,
    statement_lines: &[usize],
) -> String {
    let previous = statement_lines
        .iter()
        .copied()
        .filter(|line| *line < before_line)
        .max();
    let next = statement_lines
        .iter()
        .copied()
        .filter(|line| *line > before_line)
        .min();
    let mut nearby = Vec::new();
    if let Some(previous) = previous {
        nearby.push(format!(
            "previous top-level statement starts at line {}",
            previous
        ));
    }
    if let Some(next) = next {
        nearby.push(format!("next top-level statement starts at line {}", next));
    }
    let nearby = if nearby.is_empty() {
        "the file has no top-level statements".to_string()
    } else {
        nearby.join("; ")
    };
    format!(
        "-trust-before-line {} must be the header line of a top-level statement in `{}`; {}",
        before_line, file, nearby
    )
}

pub fn display_trusted_prefix_report_json(report: &TrustedPrefixReport) -> String {
    render_json_value(
        &JsonValue::Object(vec![
            (
                "type".to_string(),
                JsonValue::JsonString("trusted_prefix".to_string()),
            ),
            (
                "file".to_string(),
                JsonValue::JsonString(report.file.clone()),
            ),
            (
                "before_line".to_string(),
                JsonValue::Number(report.before_line),
            ),
            (
                "trusted_top_level_statements".to_string(),
                JsonValue::Number(report.trusted_top_level_statements),
            ),
            (
                "first_verified_statement_line".to_string(),
                JsonValue::Number(report.first_verified_statement_line),
            ),
        ]),
        0,
    )
}

/// Render finished user output. Internal symbol identities are always removed;
/// callers cannot opt into leaking runtime-local IDs.
pub fn render_run_source_code_output(
    runtime: &Runtime,
    stmt_results: &Vec<StmtResult>,
    runtime_error: &Option<RuntimeError>,
    _strip_free_param_tags: bool,
) -> (bool, String) {
    let mut output_text = String::new();
    for stmt_result in stmt_results.iter() {
        output_text.push('\n');
        output_text.push_str(display_stmt_exec_result_json(runtime, stmt_result, false).as_str());
        output_text.push('\n');
    }

    let ok = runtime_error.is_none();
    if let Some(error) = runtime_error {
        output_text.push('\n');
        output_text.push_str(display_runtime_error_json(runtime, error, false).as_str());
        output_text.push('\n');
    }

    if ok && !runtime.unverified_imports.is_empty() {
        output_text.push('\n');
        output_text.push_str(unverified_import_warning_json(runtime).as_str());
        output_text.push('\n');
    }

    let output_text = strip_free_param_numeric_tags_in_display(&output_text);

    if ok {
        (true, output_text)
    } else {
        (false, output_text)
    }
}

fn unverified_import_warning_json(runtime: &Runtime) -> String {
    let imports = runtime
        .unverified_imports
        .iter()
        .map(|entry| {
            JsonValue::Object(vec![
                (
                    "kind".to_string(),
                    JsonValue::JsonString(entry.kind.clone()),
                ),
                (
                    "name".to_string(),
                    JsonValue::JsonString(entry.name.clone()),
                ),
                ("line".to_string(), JsonValue::Number(entry.line_file.0)),
                (
                    "file".to_string(),
                    JsonValue::JsonString(entry.line_file.1.to_string()),
                ),
            ])
        })
        .collect();
    render_json_value(
        &JsonValue::Object(vec![
            (
                "result".to_string(),
                JsonValue::JsonString("success".to_string()),
            ),
            (
                "type".to_string(),
                JsonValue::JsonString("unverified import warning".to_string()),
            ),
            (
                "message".to_string(),
                JsonValue::JsonString(
                    "configured imports and -f prefix exports are trusted by default for faster runs; rerun with -strict to verify loaded dependencies"
                        .to_string(),
                ),
            ),
            ("unverified_imports".to_string(), JsonValue::Array(imports)),
        ]),
        0,
    )
}
