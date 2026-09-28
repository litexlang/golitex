use crate::runtime::{RuntimeError, RuntimeResult};
use std::path::PathBuf;

/// How a new_pipeline Runtime session was launched. Shared by `run` and `runtime` (no cycle).
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LaunchCommand {
    Help,
    Version,
    Repl {
        strict: bool,
    },
    Eval {
        code: String,
        session: bool,
        strict: bool,
    },
    File {
        path: PathBuf,
        session: bool,
        strict: bool,
    },
    Repository {
        path: PathBuf,
        session: bool,
        strict: bool,
    },
}

impl LaunchCommand {
    pub fn is_strict(&self) -> bool {
        match self {
            LaunchCommand::Repl { strict }
            | LaunchCommand::Eval { strict, .. }
            | LaunchCommand::File { strict, .. }
            | LaunchCommand::Repository { strict, .. } => *strict,
            LaunchCommand::Help | LaunchCommand::Version => false,
        }
    }
}

pub fn parse_launch_command(args: &[String]) -> RuntimeResult<LaunchCommand> {
    let mut session = false;
    let mut strict = false;
    let mut rest = Vec::new();
    for arg in args {
        if arg == "-session" || arg == "--session" {
            session = true;
        } else if arg == "-strict" || arg == "--strict" {
            strict = true;
        } else {
            rest.push(arg.clone());
        }
    }

    match rest.as_slice() {
        [] => Ok(LaunchCommand::Repl { strict }),
        [flag] if flag == "-help" || flag == "--help" || flag == "-h" => {
            if session || strict {
                return Err(RuntimeError::InvalidArguments(
                    "`-help` does not take `-session` or `-strict`".to_string(),
                ));
            }
            Ok(LaunchCommand::Help)
        }
        [flag] if flag == "-version" || flag == "--version" => {
            if session || strict {
                return Err(RuntimeError::InvalidArguments(
                    "`-version` does not take `-session` or `-strict`".to_string(),
                ));
            }
            Ok(LaunchCommand::Version)
        }
        [flag, value] if flag == "-e" && is_value(value) => Ok(LaunchCommand::Eval {
            code: value.clone(),
            session,
            strict,
        }),
        [flag, value] if flag == "-f" && is_value(value) => Ok(LaunchCommand::File {
            path: PathBuf::from(value),
            session,
            strict,
        }),
        [flag, value] if flag == "-r" && is_value(value) => Ok(LaunchCommand::Repository {
            path: PathBuf::from(value),
            session,
            strict,
        }),
        _ => Err(RuntimeError::InvalidArguments(
            "new_pipeline supports bare REPL, `-e <code>`, `-f <file>`, `-r <repository>`, optional `-session` / `-strict`, `-help`, `-version`"
                .to_string(),
        )),
    }
}

fn is_value(token: &str) -> bool {
    !token.is_empty() && !token.starts_with('-')
}
