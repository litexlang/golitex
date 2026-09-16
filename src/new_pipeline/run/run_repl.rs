use crate::new_pipeline::launch_command::LaunchCommand;
use super::run_command::NEW_PIPELINE_VERSION;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::new_pipeline::LITEX;
use std::io::{self, Write};

/// Interactive REPL on a fresh Runtime opened from `LaunchCommand::Repl`.
pub fn run_repl(command: LaunchCommand) -> RuntimeResult<()> {
    let mut runtime = Runtime::new(command);
    run_repl_loop(&mut runtime)
}

/// Continue a REPL in an already-open file/eval Runtime env (used by `-session`).
pub fn run_repl_loop(runtime: &mut Runtime) -> RuntimeResult<()> {
    println!("{} REPL {}", LITEX, NEW_PIPELINE_VERSION);
    println!("type `exit` or Ctrl-D to quit; end a block with a blank line");

    loop {
        let Some(code) = read_repl_block()? else {
            break;
        };
        let code_result = match runtime.run_litex_code(&code) {
            Ok(result) => result,
            Err(error) => {
                eprintln!("session_error: {}", format_runtime_error(&error));
                runtime.abort_file();
                return Err(error);
            }
        };

        if let Some(session_error) = code_result.session_error {
            eprintln!("session_error: {:?}", session_error);
            runtime.abort_file();
            return match session_error {
                super::run_command_outcome::RunSessionError::Runtime(error) => Err(error),
                other => {
                    let _ = other;
                    Ok(())
                }
            };
        }

        if code_result.success {
            println!("success");
        } else {
            println!("error");
        }
    }

    runtime.abort_file();
    Ok(())
}

fn format_runtime_error(error: &RuntimeError) -> String {
    match error {
        RuntimeError::InvalidArguments(message) => message.clone(),
        RuntimeError::Io { path, message } => format!("{}: {}", path.display(), message),
        RuntimeError::ParseError(error) => {
            format!("{} at line {} in {}", error.message, error.line, error.path)
        }
        RuntimeError::Unsupported(message)
        | RuntimeError::Invariant(message)
        | RuntimeError::Unknown(message) => message.clone(),
    }
}

fn read_repl_block() -> RuntimeResult<Option<String>> {
    let stdin = io::stdin();
    let mut buffer = String::new();
    let bin = LITEX.to_ascii_lowercase();
    loop {
        let prompt = if buffer.is_empty() {
            format!("{}> ", bin)
        } else {
            "... ".to_string()
        };
        print!("{}", prompt);
        let _ = io::stdout().flush();

        let mut line = String::new();
        let n = stdin
            .read_line(&mut line)
            .map_err(|error| RuntimeError::Io {
                path: std::path::PathBuf::from("<stdin>"),
                message: error.to_string(),
            })?;
        if n == 0 {
            if buffer.trim().is_empty() {
                return Ok(None);
            }
            return Ok(Some(buffer));
        }

        let trimmed = line.trim();
        if buffer.is_empty() && (trimmed == "exit" || trimmed == "quit" || trimmed == ":quit") {
            return Ok(None);
        }
        if trimmed.is_empty() {
            if buffer.trim().is_empty() {
                continue;
            }
            return Ok(Some(buffer));
        }

        buffer.push_str(&line);
        if buffer.lines().count() == 1 && !trimmed.ends_with(':') {
            return Ok(Some(buffer));
        }
    }
}
