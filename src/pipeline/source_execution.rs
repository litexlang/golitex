use crate::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;

pub use crate::result::StmtResult;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunOutputOptions {
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub output_language: OutputLanguage,
    pub summarize: bool,
}

impl Default for RunOutputOptions {
    fn default() -> Self {
        Self {
            output_style: OutputStyle::Normal,
            strict_mode: false,
            output_language: OutputLanguage::English,
            summarize: false,
        }
    }
}

/// Resolve a source-file target against the process working directory.
pub fn resolve_source_file_path(file_path: &str) -> Result<String, String> {
    let path = remove_windows_carriage_return(file_path);
    let absolute_path = if Path::new(path.as_str()).is_absolute() {
        PathBuf::from(path.as_str())
    } else {
        let working_directory = env::current_dir()
            .map_err(|error| format!("failed to get current working directory: {}", error))?;
        working_directory.join(path.as_str())
    };

    if absolute_path.parent().is_none() {
        return Err("could not get parent directory of file path".to_string());
    }

    absolute_path
        .to_str()
        .map(str::to_string)
        .ok_or_else(|| "file path is not valid UTF-8".to_string())
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FileRunOptions {
    pub output: RunOutputOptions,
    pub force_isolated: bool,
}

/// Run one file with an owned Runtime and render its complete output.
pub fn run_file(entry_file_path: &str, options: FileRunOptions) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.set_output_style(options.output.output_style);
    runtime.strict_mode = options.output.strict_mode;
    runtime.output_language = options.output.output_language;
    let (stmt_results, runtime_error) =
        run_file_with_project_context(entry_file_path, &mut runtime, options.force_isolated);
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if options.output.summarize {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    (ok, output)
}

/// Run a configured repository with an owned Runtime and render its complete output.
pub fn run_repository(repository_path: &str, options: RunOutputOptions) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.set_output_style(options.output_style);
    runtime.strict_mode = options.strict_mode;
    runtime.output_language = options.output_language;
    let target = match discover_repository(&mut runtime, repository_path) {
        Ok(target) => target,
        Err(error) => {
            return render_run_source_code_output(&runtime, &vec![], &Some(error), true);
        }
    };
    let (stmt_results, runtime_error) = run_repository_file_target(&mut runtime, target);
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if options.summarize {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    (ok, output)
}

pub fn run_source_code_in_file(entry_file_path: &str) -> String {
    run_file(entry_file_path, FileRunOptions::default()).1
}

// Compatibility wrappers. New callers should prefer `run_file` or
// `run_repository` with named options.
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
    run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style: output_style_from_detail_output(detail_output),
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated: false,
        },
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
    run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style: output_style_from_detail_output(detail_output),
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated,
        },
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
    run_file(
        entry_file_path,
        FileRunOptions {
            output: RunOutputOptions {
                output_style,
                strict_mode,
                output_language,
                summarize,
            },
            force_isolated,
        },
    )
    .1
}

pub fn run_source_code_in_file_with_ok(entry_file_path: &str) -> (bool, String) {
    run_file(entry_file_path, FileRunOptions::default())
}

pub fn run_source_code_in_repository_for_cli_with_summary_and_language(
    repository_path: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> String {
    run_repository(
        repository_path,
        RunOutputOptions {
            output_style: output_style_from_detail_output(detail_output),
            strict_mode,
            output_language,
            summarize,
        },
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
    run_repository(
        repository_path,
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize,
        },
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
    run_repository(
        repository_path,
        RunOutputOptions {
            output_style: output_style_from_detail_output(detail_output),
            strict_mode,
            output_language,
            summarize,
        },
    )
}

pub fn run_repository_with_output_style(
    repository_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    run_repository(
        repository_path,
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize,
        },
    )
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
    let (stmt_results, runtime_error, _, _) = run_file_with_project_context_and_trusted_prefix(
        entry_file_path,
        runtime,
        force_isolated,
        None,
    );
    (stmt_results, runtime_error)
}

pub fn run_file_with_project_context_and_trusted_prefix(
    entry_file_path: &str,
    runtime: &mut Runtime,
    force_isolated: bool,
    trust_before_line: Option<usize>,
) -> (
    Vec<StmtResult>,
    Option<RuntimeError>,
    Option<TrustedPrefixReport>,
    bool,
) {
    let path = Path::new(entry_file_path);
    let file_name = path.file_name().and_then(|name| name.to_str());
    if file_name == Some("litex.config") {
        return (
            vec![],
            Some(file_target_error(
                entry_file_path,
                "litex.config is project configuration, not executable Litex source",
            )),
            None,
            false,
        );
    }
    let mut trusted_prefix_report = None;
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
                    None,
                    false,
                )
            }
        };
        let source_code = remove_windows_carriage_return(source_code.as_str());
        let blocks =
            match Tokenizer::new().parse_blocks(source_code.as_str(), Rc::from(entry_file_path)) {
                Ok(blocks) => blocks,
                Err(error) => return (vec![], Some(error), None, false),
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
            return (
                vec![],
                Some(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        message,
                        (before_line, Rc::from(entry_file_path)),
                    ))
                    .into(),
                ),
                None,
                true,
            );
        }
        let trusted_top_level_statements = statement_lines
            .iter()
            .filter(|line| **line < before_line)
            .count();
        trusted_prefix_report = Some(TrustedPrefixReport::new(
            entry_file_path.to_string(),
            before_line,
            trusted_top_level_statements,
            before_line,
        ));
    }
    if !force_isolated {
        match discover_repository_for_file(runtime, entry_file_path) {
            Ok(Some(target)) => {
                let (stmt_results, runtime_error) = if let Some(before_line) = trust_before_line {
                    let (module_id, layer) = match target {
                        RepositoryFileTarget::Module(module_id) => {
                            (module_id, ExecutionLayer::Main)
                        }
                        RepositoryFileTarget::File { module_id, file_id } => {
                            (module_id, ExecutionLayer::File(file_id))
                        }
                    };
                    let policy = TrustedPrefixPolicy::new(module_id, layer, before_line);
                    run_repository_file_target_with_trusted_prefix(runtime, target, &policy)
                } else {
                    run_repository_file_target(runtime, target)
                };
                return (stmt_results, runtime_error, trusted_prefix_report, false);
            }
            Ok(None) => {
                return (
                    vec![],
                    Some(file_target_error(
                        entry_file_path,
                        "litex -f requires a litex.config in the same folder; use `litex -isolated -f <file>` for an isolated file",
                    )),
                    trusted_prefix_report,
                    false,
                )
            }
            Err(error) => return (vec![], Some(error), trusted_prefix_report, false),
        }
    }

    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(error) => {
            return (
                vec![],
                Some(file_target_error(
                    entry_file_path,
                    format!("could not read file: {}", error).as_str(),
                )),
                trusted_prefix_report,
                false,
            )
        }
    };
    runtime.start_isolated_source(entry_file_path);
    runtime.set_current_source_allows_inline_imports(true);
    let outcome = run_source_code_with_options(
        remove_windows_carriage_return(source_code.as_str()).as_str(),
        runtime,
        SourceRunOptions { trust_before_line },
    );
    (
        outcome.stmt_results,
        outcome.runtime_error,
        trusted_prefix_report,
        false,
    )
}

fn file_target_error(entry_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(entry_file_path)),
    ))
    .into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceRunFailureKind {
    TryStmt,
    Other,
}

pub type RunSourceFailureKind = SourceRunFailureKind;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SourceRunOptions {
    pub trust_before_line: Option<usize>,
}

pub struct SourceRunOutcome {
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
    pub failure_kind: Option<SourceRunFailureKind>,
}

impl SourceRunOutcome {
    fn success(stmt_results: Vec<StmtResult>) -> Self {
        Self {
            stmt_results,
            runtime_error: None,
            failure_kind: None,
        }
    }

    fn failure(
        stmt_results: Vec<StmtResult>,
        runtime_error: RuntimeError,
        failure_kind: SourceRunFailureKind,
    ) -> Self {
        Self {
            stmt_results,
            runtime_error: Some(runtime_error),
            failure_kind: Some(failure_kind),
        }
    }

    pub fn into_parts(
        self,
    ) -> (
        Vec<StmtResult>,
        Option<RuntimeError>,
        Option<SourceRunFailureKind>,
    ) {
        (self.stmt_results, self.runtime_error, self.failure_kind)
    }
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let outcome = run_source_code_with_options(source_code, runtime, SourceRunOptions::default());
    (outcome.stmt_results, outcome.runtime_error)
}

// Compatibility wrapper for callers that still consume the legacy tuple.
pub fn run_source_code_with_failure_kind(
    source_code: &str,
    runtime: &mut Runtime,
) -> (
    Vec<StmtResult>,
    Option<RuntimeError>,
    Option<RunSourceFailureKind>,
) {
    run_source_code_with_options(source_code, runtime, SourceRunOptions::default()).into_parts()
}

// Compatibility wrapper for callers that still consume the legacy tuple.
pub fn run_source_code_with_failure_kind_and_trusted_prefix(
    source_code: &str,
    runtime: &mut Runtime,
    trust_before_line: Option<usize>,
) -> (
    Vec<StmtResult>,
    Option<RuntimeError>,
    Option<RunSourceFailureKind>,
) {
    run_source_code_with_options(source_code, runtime, SourceRunOptions { trust_before_line })
        .into_parts()
}

pub fn run_source_code_with_options(
    source_code: &str,
    runtime: &mut Runtime,
    options: SourceRunOptions,
) -> SourceRunOutcome {
    if let Err(error) = require_active_source_context(runtime) {
        return SourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
    }

    let blocks = match tokenize_source_code(source_code, runtime) {
        Ok(blocks) => blocks,
        Err((error, failure_kind)) => {
            return SourceRunOutcome::failure(vec![], error, failure_kind);
        }
    };
    if let Some(before_line) = options.trust_before_line {
        if let Err(error) = validate_trusted_prefix_boundary(&blocks, runtime, before_line) {
            return SourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
        }
    }

    execute_source_blocks(blocks, runtime, options)
}

fn require_active_source_context(runtime: &Runtime) -> Result<(), RuntimeError> {
    if runtime.has_active_execution_frame() {
        return Ok(());
    }

    Err(ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
        "runtime has no active source context; initialize a file or repository before running source"
            .to_string(),
    ))
    .into())
}

fn tokenize_source_code(
    source_code: &str,
    runtime: &Runtime,
) -> Result<Vec<TokenBlock>, (RuntimeError, SourceRunFailureKind)> {
    let starts_with_try = source_code
        .lines()
        .find(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .is_some_and(|line| line.trim_end() == "try:");
    Tokenizer::new()
        .parse_blocks(source_code, runtime.current_file_path_rc())
        .map_err(|error| (error, failure_kind_for_try(starts_with_try)))
}

fn validate_trusted_prefix_boundary(
    blocks: &[TokenBlock],
    runtime: &Runtime,
    before_line: usize,
) -> Result<(), RuntimeError> {
    let statement_lines = blocks
        .iter()
        .map(|block| block.line_file.0)
        .collect::<Vec<_>>();
    if statement_lines.contains(&before_line) {
        return Ok(());
    }

    let message = trusted_prefix_boundary_error_message(
        runtime.current_file_path_rc().as_ref(),
        before_line,
        &statement_lines,
    );
    Err(
        ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
            message,
            (before_line, runtime.current_file_path_rc()),
        ))
        .into(),
    )
}

fn execute_source_blocks(
    blocks: Vec<TokenBlock>,
    runtime: &mut Runtime,
    options: SourceRunOptions,
) -> SourceRunOutcome {
    let profile_repository_run = std::env::var_os("LITEX_PROFILE_REPOSITORY").is_some();
    let mut stmt_results: Vec<StmtResult> = Vec::new();
    for mut block in blocks {
        let statement_start = profile_repository_run.then(Instant::now);
        let parsing_try_stmt = block.current_token_is_equal_to(TRY);
        let stmt = match runtime.parse_stmt(&mut block) {
            Ok(stmt) => stmt,
            Err(error) => {
                return SourceRunOutcome::failure(
                    stmt_results,
                    error,
                    failure_kind_for_try(parsing_try_stmt),
                );
            }
        };
        let executing_try_stmt = matches!(&stmt, Stmt::ProofBlock(ProofBlockStmt::TryStmt(_)));
        let trusted_prefix_statement = options
            .trust_before_line
            .is_some_and(|before_line| stmt.line_file().0 < before_line);
        let previous_execution_mode = trusted_prefix_statement
            .then(|| runtime.replace_current_execution_mode(ExecutionMode::Trusted));
        let result = match if options.trust_before_line.is_some() {
            execute_top_level_statement_in_trusted_prefix_run(&stmt, runtime)
        } else {
            execute_top_level_statement(&stmt, runtime)
        } {
            Ok(result) => result,
            Err(error) => {
                if let Some(previous_execution_mode) = previous_execution_mode {
                    runtime.replace_current_execution_mode(previous_execution_mode);
                }
                return SourceRunOutcome::failure(
                    stmt_results,
                    error,
                    failure_kind_for_try(executing_try_stmt),
                );
            }
        };
        if let Some(previous_execution_mode) = previous_execution_mode {
            runtime.replace_current_execution_mode(previous_execution_mode);
        }
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

    SourceRunOutcome::success(stmt_results)
}

fn failure_kind_for_try(is_try_stmt: bool) -> SourceRunFailureKind {
    if is_try_stmt {
        SourceRunFailureKind::TryStmt
    } else {
        SourceRunFailureKind::Other
    }
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

    if ok && !runtime.unverified_imports().is_empty() {
        output_text.push('\n');
        output_text.push_str(unverified_import_warning_json(runtime).as_str());
        output_text.push('\n');
    }

    let output_text = strip_free_param_numeric_tags_in_display(&output_text);

    (ok, output_text)
}

fn unverified_import_warning_json(runtime: &Runtime) -> String {
    let imports = runtime
        .unverified_imports()
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

#[cfg(test)]
#[path = "../../tests/unit/pipeline/source_execution/source_run_tests.rs"]
mod source_run_tests;
