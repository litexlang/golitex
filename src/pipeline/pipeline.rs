use crate::pipeline::display::{display_runtime_error_json, display_stmt_exec_result_json};
use crate::pipeline::run_stmt_at_global_env;
use crate::prelude::*;
use std::fs;

pub use crate::result::StmtResult;

pub fn run_source_code_in_file(entry_file_path: &str) -> String {
    let source_code = match fs::read_to_string(entry_file_path) {
        Ok(content) => content,
        Err(read_error) => panic!("Could not read file {:?}: {}", entry_file_path, read_error),
    };
    run_source_code_with_output(&source_code, entry_file_path).1
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
    run_source_code_with_output(&source_code, entry_file_path)
}

fn run_source_code_with_output(source_code: &str, entry_label: &str) -> (bool, String) {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new_with_builtin_code();
    runtime.new_file_path_new_env_new_name_scope(entry_label);
    let (stmt_results, runtime_error) = run_source_code(normalized_source.as_str(), &mut runtime);
    render_run_source_code_output(&runtime, &stmt_results, &runtime_error)
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let blocks = match TokenBlock::parse_blocks(
        source_code,
        runtime.module_manager.current_file_path_rc(),
    ) {
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

pub fn render_run_source_code_output(
    runtime: &Runtime,
    stmt_results: &Vec<StmtResult>,
    runtime_error: &Option<RuntimeError>,
) -> (bool, String) {
    let mut output_text = String::new();
    for stmt_result in stmt_results.iter() {
        output_text.push('\n');
        output_text.push_str(display_stmt_exec_result_json(runtime, stmt_result).as_str());
        output_text.push('\n');
    }

    if let Some(error) = runtime_error {
        output_text.push('\n');
        output_text.push_str(display_runtime_error_json(runtime, error).as_str());
        output_text.push('\n');
        return (false, output_text);
    }

    (true, output_text)
}
