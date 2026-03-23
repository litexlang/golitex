use crate::environment::Environment;
use crate::execute::Runtime;
use crate::module_manager::ModuleManager;
use crate::parse::TokenBlock;
use crate::runtime::RuntimeContext;
use crate::stmt::Stmt;
use std::fs;
use std::io::{self, BufRead, Write};

pub fn run_source_code_in_file(entrance_file_path: &str) -> String {
    let source_code = fs::read_to_string(entrance_file_path).expect("Could not read file");
    run_source_code(&source_code, entrance_file_path)
}

pub fn run_source_code_from_string(source_code: &str, entrance_label: &str) -> String {
    let normalized_source = remove_windows_carriage_return(source_code);
    run_source_code(normalized_source.as_str(), entrance_label)
}

fn remove_windows_carriage_return(source_code: &str) -> String {
    source_code.replace('\r', "")
}

pub fn run_source_code(source_code: &str, entrance_file_path: &str) -> String {
    let mut module_manager = ModuleManager::new_empty_module_manager(entrance_file_path);
    let mut builtin_environment = Environment::new_empty_env();

    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );

    let blocks = match TokenBlock::parse_blocks(source_code, 0) {
        Ok(b) => b,
        Err(e) => return format!("\n{}\n", runtime_context.display_error(&e.into())),
    };

    let mut out = String::new();
    let mut executor = Runtime::new(&mut runtime_context);
    for mut block in blocks {
        let stmt: Stmt = {
            match executor.parse_stmt(&mut block) {
                Ok(s) => s,
                Err(e) => {
                    out.push_str(
                        format!("\n{}\n", executor.runtime_context.display_error(&e.into()))
                            .as_str(),
                    );
                    return out;
                }
            }
        };
        let result = match executor.exec_stmt(&stmt) {
            Ok(r) => r,
            Err(e) => {
                out.push_str(
                    format!("\n{}\n", executor.runtime_context.display_error(&e)).as_str(),
                );
                return out;
            }
        };
        out.push('\n');
        out.push_str(executor.runtime_context.display_result(&result).as_str());
        out.push('\n');
    }
    out
}

/// Interactive REPL: one persistent [`RuntimeContext`] for the session (same as running a file line by line).
///
/// Parse errors use normal `&mut runtime_context`. After a successful parse, execution uses a raw pointer for
/// one iteration only so the borrow checker accepts a loop; this matches the usual “one `Runtime` per line”
/// pattern while keeping `module_manager`, `builtin_environment`, and environment stack across inputs.
pub fn run_repl_loop(version_banner: &str) {
    println!("Litex kernel REPL (litex {})", version_banner);
    println!("Empty lines are skipped. Ctrl+D to exit.\n");

    let mut module_manager = ModuleManager::new_empty_module_manager("repl");
    let mut builtin_environment = Environment::new_empty_env();
    let mut runtime_context = RuntimeContext::new_empty_runtime_context_with_one_env(
        &mut module_manager,
        &mut builtin_environment,
    );

    let stdin_handle = io::stdin();
    let mut line_reader = stdin_handle.lock();
    let mut line_buffer = String::new();

    loop {
        print!("litex> ");
        if io::stdout().flush().is_err() {
            break;
        }

        line_buffer.clear();
        let bytes_read = match line_reader.read_line(&mut line_buffer) {
            Ok(byte_count) => byte_count,
            Err(read_error) => {
                eprintln!("stdin read error: {}", read_error);
                break;
            }
        };

        if bytes_read == 0 {
            println!();
            break;
        }

        let trimmed_line = line_buffer.trim();
        if trimmed_line.is_empty() {
            continue;
        }

        let normalized_source = remove_windows_carriage_return(trimmed_line);

        let blocks = match TokenBlock::parse_blocks(normalized_source.as_str(), 0) {
            Ok(parsed_blocks) => parsed_blocks,
            Err(parse_block_error) => {
                let stmt_error = parse_block_error.into();
                let error_string = runtime_context.display_error(&stmt_error);
                println!("\n{}\n", error_string);
                continue;
            }
        };

        // SAFETY: `ctx_ptr` is created from `&mut runtime_context` for this statement only. Inside the
        // block, `Runtime` is the sole accessor until it is dropped. We do not use `runtime_context` by
        // name while `executor` is alive.
        let ctx_ptr: *mut RuntimeContext<'_> = &mut runtime_context;
        let mut output_chunk = String::new();
        unsafe {
            let ctx_ref = &mut *ctx_ptr;
            let mut executor = Runtime::new(ctx_ref);
            for mut block in blocks {
                let stmt: Stmt = match executor.parse_stmt(&mut block) {
                    Ok(statement) => statement,
                    Err(parse_stmt_error) => {
                        let message = executor
                            .runtime_context
                            .display_error(&parse_stmt_error.into());
                        output_chunk.push_str(&format!("\n{}\n", message));
                        break;
                    }
                };

                let exec_result = match executor.exec_stmt(&stmt) {
                    Ok(result) => result,
                    Err(exec_error) => {
                        let message = executor.runtime_context.display_error(&exec_error);
                        output_chunk.push_str(&format!("\n{}\n", message));
                        break;
                    }
                };

                output_chunk.push('\n');
                output_chunk.push_str(
                    executor
                        .runtime_context
                        .display_result(&exec_result)
                        .as_str(),
                );
                output_chunk.push('\n');
            }
        }

        let trimmed_output = output_chunk.trim();
        if !trimmed_output.is_empty() {
            println!("{}", trimmed_output);
        }
    }
}
