//! CLI stdout writes with explicit I/O handling.

use crate::runtime::{RuntimeError, RuntimeResult};
use std::fmt::Arguments;
use std::io::{self, Write};
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
            write_stdout(format_args!("{}", result.source))
        }
        _ => {
            if let Some(json) = outcome.normal_json() {
                write_stdout(format_args!("{json}\n"))?;
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
        return write_stdout(format_args!("{json}\n"));
    }
    let diagnostic = match (command, error) {
        (
            Some(crate::launch_command::LaunchCommand::CompileToLean { .. }),
            RuntimeError::Unsupported(message),
        ) => message.clone(),
        (Some(crate::launch_command::LaunchCommand::CompileToLean { .. }), _) => {
            format!("phase=compile: {error}")
        }
        _ => error.to_string(),
    };
    writeln!(io::stderr().lock(), "{diagnostic}").map_err(|error| RuntimeError::Io {
        path: PathBuf::from("<stderr>"),
        message: error.to_string(),
    })
}
