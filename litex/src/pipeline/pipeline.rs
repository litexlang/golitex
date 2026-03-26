use crate::common::keywords::BUILTIN;
use crate::execute::Runtime;
use crate::module_manager::ModuleManager;
use crate::parse::TokenBlock;
use crate::runtime::RuntimeContext;
use crate::runtime::BUILTIN_ENV_CODE;
use crate::stmt::Stmt;
use std::fs;
use std::io::{self, BufRead, Write};

pub fn run_source_code_in_file_and_return_string(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code_and_return_string(&source_code, entrance_file_path)
}

pub fn run_source_code_in_file_and_return_json_string(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code_and_return_json_string(&source_code, entrance_file_path)
}

pub fn run_source_code_and_return_string(source_code: &str, entrance_label: &str) -> String {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut module_manager = ModuleManager::new_empty_module_manager(BUILTIN);
    let mut runtime_context =
        RuntimeContext::new_empty_runtime_context_with_one_env(&mut module_manager);
    let mut runtime = Runtime::new(&mut runtime_context);
    run_source_code(normalized_source.as_str(), &mut runtime, false);
    runtime
        .runtime_context
        .module_manager
        .new_file_path(entrance_label);
    run_source_code(BUILTIN_ENV_CODE, &mut runtime, false)
}

pub fn run_source_code_and_return_json_string(source_code: &str, entrance_label: &str) -> String {
    let normalized_source = remove_windows_carriage_return(source_code);
    let mut module_manager = ModuleManager::new_empty_module_manager(BUILTIN);
    let mut runtime_context =
        RuntimeContext::new_empty_runtime_context_with_one_env(&mut module_manager);
    let mut runtime = Runtime::new(&mut runtime_context);
    run_source_code(BUILTIN_ENV_CODE, &mut runtime, true);
    runtime
        .runtime_context
        .module_manager
        .new_file_path(entrance_label);
    run_source_code(normalized_source.as_str(), &mut runtime, true)
}

fn remove_windows_carriage_return(source_code: &str) -> String {
    source_code.replace('\r', "")
}

pub fn run_source_code(
    source_code: &str,
    runtime: &mut Runtime,
    should_output_json: bool,
) -> String {
    let blocks = match TokenBlock::parse_blocks(
        source_code,
        runtime.runtime_context.module_manager.current_file_index,
    ) {
        Ok(b) => b,
        Err(e) => {
            let runtime_error = e.into();
            if should_output_json {
                return format!(
                    "\n{}\n",
                    runtime
                        .runtime_context
                        .display_error_json_string(&runtime_error)
                );
            }
            return format!(
                "\n{}\n",
                runtime.runtime_context.display_error(&runtime_error)
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
                        out.push_str(
                            format!(
                                "\n{}\n",
                                runtime
                                    .runtime_context
                                    .display_error_json_string(&runtime_error)
                            )
                            .as_str(),
                        );
                    } else {
                        out.push_str(
                            format!(
                                "\n{}\n",
                                runtime.runtime_context.display_error(&runtime_error)
                            )
                            .as_str(),
                        );
                    }
                    return out;
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
                        format!("\n{}\n", runtime.runtime_context.display_error(&e)).as_str(),
                    );
                }
                return out;
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

    out
}

pub fn run_repl_loop_and_return_string(version_banner: &str) {
    run_repl_loop_internal(version_banner, false);
}

pub fn run_repl_loop_and_return_json_string(version_banner: &str) {
    run_repl_loop_internal(version_banner, true);
}

fn run_repl_loop_internal(version_banner: &str, should_output_json: bool) {
    let stdin_handle = io::stdin();
    let stdout_handle = io::stdout();
    let mut stdin_locked = stdin_handle.lock();
    let mut stdout_locked = stdout_handle.lock();
    match run_repl_loop_with_readers(
        version_banner,
        &mut stdin_locked,
        &mut stdout_locked,
        should_output_json,
    ) {
        Ok(()) => {}
        Err(write_error) => {
            eprintln!("repl output error: {}", write_error);
        }
    }
}

fn run_repl_loop_with_readers<R, W>(
    version_banner: &str,
    stdin_reader: &mut R,
    stdout_writer: &mut W,
    should_output_json: bool,
) -> io::Result<()>
where
    R: BufRead,
    W: Write,
{
    writeln!(stdout_writer, "Litex version {}", version_banner)?;
    writeln!(stdout_writer, "Copyright (C) 2024-2026 Jiachen Shen")?;
    writeln!(stdout_writer, "website: https://litexlang.com")?;
    writeln!(stdout_writer, "Ctrl+D to exit.\n")?;

    let mut module_manager = ModuleManager::new_empty_module_manager(BUILTIN);
    let mut runtime_context =
        RuntimeContext::new_empty_runtime_context_with_one_env(&mut module_manager);

    let mut runtime = Runtime::new(&mut runtime_context);

    run_source_code(BUILTIN_ENV_CODE, &mut runtime, true);
    runtime.runtime_context.module_manager.new_file_path("repl");

    let mut line_buffer = String::new();

    loop {
        write!(stdout_writer, ">>> ")?;
        stdout_writer.flush()?;

        line_buffer.clear();
        let bytes_read = match stdin_reader.read_line(&mut line_buffer) {
            Ok(byte_count) => byte_count,
            Err(read_error) => {
                writeln!(stdout_writer, "stdin read error: {}", read_error)?;
                break;
            }
        };

        if bytes_read == 0 {
            writeln!(stdout_writer)?;
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            continue;
        }

        let normalized_source = remove_windows_carriage_return(trimmed_line);

        let blocks = match TokenBlock::parse_blocks(
            normalized_source.as_str(),
            runtime.runtime_context.module_manager.current_file_index,
        ) {
            Ok(parsed_blocks) => parsed_blocks,
            Err(parse_block_error) => {
                let stmt_error = parse_block_error.into();
                let error_string = if should_output_json {
                    runtime
                        .runtime_context
                        .display_error_json_string(&stmt_error)
                } else {
                    runtime.runtime_context.display_error(&stmt_error)
                };
                writeln!(stdout_writer)?;
                writeln!(stdout_writer, "{}", error_string)?;
                writeln!(stdout_writer)?;
                break;
            }
        };

        let mut output_chunk = String::new();
        for mut block in blocks {
            let stmt: Stmt = match runtime.parse_stmt(&mut block) {
                Ok(statement) => statement,
                Err(parse_stmt_error) => {
                    let runtime_error = parse_stmt_error.into();
                    let message = if should_output_json {
                        runtime
                            .runtime_context
                            .display_error_json_string(&runtime_error)
                    } else {
                        runtime.runtime_context.display_error(&runtime_error)
                    };
                    output_chunk.push_str(&format!("\n{}\n", message));
                    break;
                }
            };

            let exec_result = match runtime.exec_stmt(&stmt) {
                Ok(result) => result,
                Err(exec_error) => {
                    let message = if should_output_json {
                        runtime
                            .runtime_context
                            .display_error_json_string(&exec_error)
                    } else {
                        runtime.runtime_context.display_error(&exec_error)
                    };
                    output_chunk.push_str(&format!("\n{}\n", message));
                    break;
                }
            };

            output_chunk.push('\n');
            if should_output_json {
                output_chunk.push_str(
                    runtime
                        .runtime_context
                        .display_result_json_string(&exec_result)
                        .as_str(),
                );
            } else {
                output_chunk.push_str(
                    runtime
                        .runtime_context
                        .display_result(&exec_result)
                        .as_str(),
                );
            }
            output_chunk.push('\n');
        }

        let trimmed_output = output_chunk.trim();
        if !trimmed_output.is_empty() {
            writeln!(stdout_writer, "{}", trimmed_output)?;
        }
    }

    Ok(())
}
