use crate::pipeline::display::{display_runtime_error_json, display_stmt_exec_result_json};
use crate::pipeline::summary::display_run_summary_json_with_runtime;
use crate::pipeline::{run_repository_file_target, run_stmt_at_global_env};
use crate::prelude::*;
use std::fs;
use std::path::Path;
use std::rc::Rc;

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
    runtime.isolated = false;
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
    if !force_isolated {
        match discover_repository_for_file(runtime, entry_file_path) {
            Ok(Some(target)) => return run_repository_file_target(runtime, target),
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
    run_source_code(
        remove_windows_carriage_return(source_code.as_str()).as_str(),
        runtime,
    )
}

fn file_target_error(entry_file_path: &str, message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from(entry_file_path)),
    ))
    .into()
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
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
        );
    }

    let mut tokenizer = Tokenizer::new();
    let current_file_path = runtime.current_file_path_rc();
    let blocks = match tokenizer.parse_blocks(source_code, current_file_path) {
        Ok(b) => b,
        Err(e) => {
            return (vec![], Some(e));
        }
    };

    let mut stmt_results: Vec<StmtResult> = Vec::new();
    for mut block in blocks {
        let stmt: Stmt = {
            match runtime.parse_stmt(&mut block) {
                Ok(s) => s,
                Err(e) => {
                    return (stmt_results, Some(e));
                }
            }
        };
        let result = match run_stmt_at_global_env(&stmt, runtime) {
            Ok(r) => r,
            Err(e) => {
                return (stmt_results, Some(e));
            }
        };
        stmt_results.push(result);
    }

    (stmt_results, None)
}

/// When `strip_free_param_tags` is true, run [`strip_free_param_numeric_tags_in_display`] on the full
/// concatenated output. Use false in `main_test` to print raw `~` tags for debugging.
pub fn render_run_source_code_output(
    runtime: &Runtime,
    stmt_results: &Vec<StmtResult>,
    runtime_error: &Option<RuntimeError>,
    strip_free_param_tags: bool,
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

    let output_text = if strip_free_param_tags {
        strip_free_param_numeric_tags_in_display(&output_text)
    } else {
        output_text
    };

    if ok {
        (true, output_text)
    } else {
        (false, output_text)
    }
}
