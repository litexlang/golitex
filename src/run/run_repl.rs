use super::output::{write_stderr, write_stdout};
use super::run_command::VERSION;
use super::run_command_outcome::RunLitexCodeResult;
use crate::launch_command::LaunchCommand;
use crate::run_module::{mount_cwd_config, MountCwdConfigOutcome};
use crate::runtime::{CodeSource, Runtime, RuntimeError, RuntimeResult};
use crate::LITEX;
use std::io::{self, IsTerminal};

/// Interactive REPL: mount cwd `litex.config` when present (else empty), then loop.
pub fn run_repl(command: LaunchCommand) -> RuntimeResult<()> {
    let mut runtime = Runtime::new(command);
    // Drop placeholder Repl env so mount can open export files.
    runtime.abort_source();

    match mount_cwd_config(&mut runtime)? {
        MountCwdConfigOutcome::Done => {}
        MountCwdConfigOutcome::SessionError(session_error) => {
            return Err(mount_session_error_to_runtime_error(session_error));
        }
    }

    runtime.begin_source(CodeSource::Repl);
    let mut turns = Vec::new();
    let result = run_repl_loop(&mut runtime, &mut turns);
    runtime.abort_source();
    result
}

/// Continue a REPL in an already-open file/eval Runtime env (used by `-session`).
/// Each block emits one Normal run JSON on stdout (`target: "repl"`). Human
/// prompts go to stderr so stdout stays JSON-only. Rejected inputs leave the
/// Session open. Accepted and rejected turns are appended to `turns` for the
/// caller's final session snapshot.
pub fn run_repl_loop(
    runtime: &mut Runtime,
    turns: &mut Vec<RunLitexCodeResult>,
) -> RuntimeResult<()> {
    runtime.current_file = CodeSource::Repl;
    write_repl_banner()?;

    loop {
        let Some(code) = read_repl_block()? else {
            break;
        };
        let code_result = match runtime.run_litex_code(&code) {
            Ok(result) => result,
            Err(error) => return Err(error),
        };

        if let Some(session_error) = code_result.session_error {
            return Err(mount_session_error_to_runtime_error(session_error));
        }

        write_stdout(format_args!(
            "{}\n",
            crate::json_output::emit_run_normal(&code_result, runtime, "repl", None)
        ))?;
        turns.push(code_result);
    }

    Ok(())
}

fn write_repl_banner() -> RuntimeResult<()> {
    // Keep stdout JSON-only; banner is human UX on stderr.
    write_stderr(format_args!("{} REPL {}\n", LITEX, VERSION))?;
    write_stderr(format_args!(
        "type `exit` or Ctrl-D to quit; end a block with a blank line\n"
    ))
}

fn mount_session_error_to_runtime_error(
    session_error: super::run_command_outcome::RunSessionError,
) -> RuntimeError {
    match session_error {
        super::run_command_outcome::RunSessionError::Runtime(error) => error,
        super::run_command_outcome::RunSessionError::FailToImport(failure) => {
            RuntimeError::InvalidArguments(format!(
                "failed to import project from cwd `litex.config`: {failure}"
            ))
        }
    }
}

#[cfg(test)]
#[test]
fn internal_error_repl_names_litex_and_preserves_the_conflict_reason() {
    let error = RuntimeError::InternalBug("merge identifier conflict".into());
    assert_eq!(
        error.to_string(),
        "internal_bug: Litex internal bug: merge identifier conflict",
    );
    assert_eq!(
        super::run_command_outcome::RunSessionError::Runtime(error).to_string(),
        "internal_bug: Litex internal bug: merge identifier conflict",
    );
}

fn read_repl_block() -> RuntimeResult<Option<String>> {
    let stdin = io::stdin();
    let mut buffer = String::new();
    let bin = LITEX.to_ascii_lowercase();
    let show_prompt = io::stderr().is_terminal() && stdin.is_terminal();
    loop {
        if show_prompt {
            let prompt = if buffer.is_empty() {
                format!("{}> ", bin)
            } else {
                "... ".to_string()
            };
            write_stderr(format_args!("{}", prompt))?;
        }

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
