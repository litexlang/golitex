use crate::common::helper::remove_windows_carriage_return;
use crate::execute::Runtime;
use crate::parse::TokenBlock;
use crate::runtime::builtin_env_code;
use crate::stmt::Stmt;
use std::fs;

pub fn run_source_code_in_file_and_return_string(entrance_file_path: &str) -> String {
    run_source_code_in_file_and_return_json_string(entrance_file_path)
}

pub fn run_source_code_in_file_and_return_json_string(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code_and_return_json_string(&source_code, entrance_file_path)
}

fn run_source_code_and_return_json_string(source_code: &str, entrance_label: &str) -> String {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut runtime = Runtime::new();
    let (ok, msg) = run_source_code(builtin_env_code().as_str(), &mut runtime, true);
    if !ok {
        return format!("builtin code execution failed: {}", msg);
    }
    runtime.new_file_path_new_env_new_name_scope(entrance_label);
    run_source_code(normalized_source.as_str(), &mut runtime, true).1
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
    should_output_json: bool,
) -> (bool, String) {
    let blocks = match TokenBlock::parse_blocks(
        source_code,
        runtime.runtime_context.module_manager.current_file_index,
    ) {
        Ok(b) => b,
        Err(e) => {
            let runtime_error = e.into();
            if should_output_json {
                return (
                    false,
                    format!(
                        "\n{}\n",
                        runtime
                            .runtime_context
                            .display_error_json_string(&runtime_error)
                    ),
                );
            }
            return (
                false,
                format!(
                    "\n{}\n",
                    runtime
                        .runtime_context
                        .display_error_with_label_and_location(&runtime_error)
                ),
            );
        }
    };

    let mut out = String::new();
    for mut block in blocks {
        let stmt: Stmt = {
            match runtime.parse_stmt(&mut block) {
                Ok(s) => s,
                Err(e) => {
                    let runtime_error = e.into();
                    if should_output_json {
                        out.push_str(&format!(
                            "\n{}\n",
                            runtime
                                .runtime_context
                                .display_error_json_string(&runtime_error)
                        ));
                    } else {
                        out.push_str(&format!(
                            "\n{}\n",
                            runtime
                                .runtime_context
                                .display_error_with_label_and_location(&runtime_error)
                        ));
                    }
                    return (false, out);
                }
            }
        };
        let result = match runtime.exec_stmt(&stmt) {
            Ok(r) => r,
            Err(e) => {
                if should_output_json {
                    out.push_str(
                        format!(
                            "\n{}\n",
                            runtime.runtime_context.display_error_json_string(&e)
                        )
                        .as_str(),
                    );
                } else {
                    out.push_str(
                        format!(
                            "\n{}\n",
                            runtime
                                .runtime_context
                                .display_error_with_label_and_location(&e)
                        )
                        .as_str(),
                    );
                }
                return (false, out);
            }
        };
        out.push('\n');
        if should_output_json {
            out.push_str(
                runtime
                    .runtime_context
                    .display_result_json_string(&result)
                    .as_str(),
            );
        } else {
            out.push_str(runtime.runtime_context.display_result(&result).as_str());
        }
        out.push('\n');
    }

    (true, out)
}
