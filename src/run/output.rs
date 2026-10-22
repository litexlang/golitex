//! CLI stdout writes with explicit I/O handling.

use crate::runtime::{RuntimeError, RuntimeResult};
use std::fmt::Arguments;
use std::io::{self, IsTerminal, Write};
use std::path::PathBuf;

/// A closed downstream reader discards output without changing verification's
/// exit status. Other output errors remain ordinary runtime I/O errors.
pub fn write_stdout(text: Arguments<'_>) -> RuntimeResult<()> {
    let mut stdout = io::stdout().lock();
    match stdout.write_fmt(text).and_then(|_| stdout.flush()) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(()),
        Err(error) => Err(RuntimeError::Io {
            path: PathBuf::from("<stdout>"),
            message: error.to_string(),
        }),
    }
}

/// Render each command's output contract through the common CLI entrypoint.
pub fn write_command_outcome(outcome: &crate::run::RunCommandOutcome) -> RuntimeResult<()> {
    match outcome {
        crate::run::RunCommandOutcome::CompileToLean(result) => {
            if result.success {
                write_stdout(format_args!("{}", result.source))
            } else {
                writeln!(io::stderr().lock(), "{}", result.source).map_err(|error| {
                    RuntimeError::Io {
                        path: PathBuf::from("<stderr>"),
                        message: error.to_string(),
                    }
                })
            }
        }
        _ => {
            if let Some(json) = outcome.normal_json() {
                write_stdout(format_args!("{json}\n"))?;
            }
            let run = match outcome {
                crate::run::RunCommandOutcome::RunFile(result) => Some(&result.run),
                crate::run::RunCommandOutcome::RunEval(result) => Some(&result.run),
                crate::run::RunCommandOutcome::RunRepo(result) => Some(&result.run),
                _ => None,
            };
            if io::stderr().is_terminal() {
                if let Some(crate::run::RunSessionError::Runtime(RuntimeError::ParseError(error))) =
                    run.and_then(|run| run.session_error.as_ref())
                {
                    write_stderr(format_args!("{}\n", error.diagnostic()))?;
                }
            }
            Ok(())
        }
    }
}

/// Keep command-specific error presentation alongside successful output.
pub fn write_command_error(
    command: Option<&crate::launch_command::LaunchCommand>,
    error: &RuntimeError,
) -> RuntimeResult<()> {
    if let Some(json) =
        command.and_then(|command| crate::json_output::emit_command_error(command, error))
    {
        write_stdout(format_args!("{json}\n"))?;
        if io::stderr().is_terminal() {
            if let RuntimeError::ParseError(error) = error {
                write_stderr(format_args!("{}\n", error.diagnostic()))?;
            }
        }
        return Ok(());
    }
    let diagnostic = match (command, error) {
        (_, RuntimeError::ParseError(error)) => error.diagnostic(),
        (
            Some(crate::launch_command::LaunchCommand::CompileToLean { .. }),
            RuntimeError::Unsupported(message),
        ) => message.clone(),
        (Some(crate::launch_command::LaunchCommand::CompileToLean { .. }), _) => {
            format!("phase=compile: {error}")
        }
        _ => error.to_string(),
    };
    write_stderr(format_args!("{diagnostic}\n"))
}

pub(crate) fn write_stderr(text: Arguments<'_>) -> RuntimeResult<()> {
    let mut stderr = io::stderr().lock();
    match stderr.write_fmt(text).and_then(|_| stderr.flush()) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::BrokenPipe => Ok(()),
        Err(error) => Err(RuntimeError::Io {
            path: PathBuf::from("<stderr>"),
            message: error.to_string(),
        }),
    }
}
