use crate::pipeline::display::{display_runtime_error_json, display_stmt_exec_result_json};
use crate::pipeline::run_stmt_at_global_env;
use crate::pipeline::summary::display_run_summary_json_with_runtime;
use crate::prelude::*;
use std::fs;
use std::path::Path;
use std::rc::Rc;

pub use crate::result::StmtResult;

pub fn run_source_code_in_file(entry_file_path: &str) -> String {
    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(read_error) => panic!("Could not read file {:?}: {}", entry_file_path, read_error),
    };
    run_source_code_with_output(
        &source_code,
        entry_file_path,
        false,
        false,
        OutputLanguage::English,
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
    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(read_error) => panic!("Could not read file {:?}: {}", entry_file_path, read_error),
    };
    run_source_code_with_output(
        &source_code,
        entry_file_path,
        detail_output,
        strict_mode,
        output_language,
        summarize,
    )
    .1
}

pub fn run_source_code_in_file_with_ok(entry_file_path: &str) -> (bool, String) {
    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(read_error) => {
            return (
                false,
                format!("Could not read file {:?}: {}", entry_file_path, read_error),
            );
        }
    };
    run_source_code_with_output(
        &source_code,
        entry_file_path,
        false,
        false,
        OutputLanguage::English,
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
    run_repository_with_output(
        repository_path,
        detail_output,
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
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.detail_output = detail_output;
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let main_file_path = match discover_repository(&mut runtime, repository_path) {
        Ok(path) => path,
        Err(error) => {
            return render_run_source_code_output(&runtime, &vec![], &Some(error), true);
        }
    };
    let source_code = match fs::read_to_string(&main_file_path) {
        Ok(content) => content,
        Err(error) => {
            let runtime_error = ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                format!("failed to read repository main.lit: {}", error),
                (0, Rc::from(main_file_path.as_str())),
            ))
            .into();
            return render_run_source_code_output(&runtime, &vec![], &Some(runtime_error), true);
        }
    };
    let normalized_source = remove_windows_carriage_return(&source_code);
    let (stmt_results, runtime_error) = run_source_code(&normalized_source, &mut runtime);
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

fn run_source_code_with_output(
    source_code: &str,
    entry_label: &str,
    detail_output: bool,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize: bool,
) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    runtime.detail_output = detail_output;
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let (stmt_results, runtime_error) = if Path::new(entry_label)
        .file_name()
        .and_then(|name| name.to_str())
        == Some("mod.lit")
    {
        (
            vec![],
            Some(
                ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "mod.lit is a module declaration file; run the project with -r".to_string(),
                    (0, Rc::from(entry_label)),
                ))
                .into(),
            ),
        )
    } else {
        run_source_code(normalized_source.as_str(), &mut runtime)
    };
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

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
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
