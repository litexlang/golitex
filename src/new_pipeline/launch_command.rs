use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult};
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

#[cfg(test)]
mod tests {
    use super::*;

    fn args(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn parses_eval_command() {
        let command = parse_launch_command(&args(&["-e", "1 + 1 = 2"])).unwrap();
        assert_eq!(
            command,
            LaunchCommand::Eval {
                code: "1 + 1 = 2".to_string(),
                session: false,
                strict: false,
            }
        );
    }

    #[test]
    fn parses_session_and_strict_with_file() {
        assert_eq!(
            parse_launch_command(&args(&["-strict", "-f", "a.lit", "-session"])).unwrap(),
            LaunchCommand::File {
                path: PathBuf::from("a.lit"),
                session: true,
                strict: true,
            }
        );
        assert_eq!(
            parse_launch_command(&args(&["-session", "-f", "a.lit"])).unwrap(),
            LaunchCommand::File {
                path: PathBuf::from("a.lit"),
                session: true,
                strict: false,
            }
        );
    }

    #[test]
    fn parses_help_version_and_repl() {
        assert_eq!(
            parse_launch_command(&args(&[])).unwrap(),
            LaunchCommand::Repl { strict: false }
        );
        assert_eq!(
            parse_launch_command(&args(&["-session"])).unwrap(),
            LaunchCommand::Repl { strict: false }
        );
        assert_eq!(
            parse_launch_command(&args(&["-strict"])).unwrap(),
            LaunchCommand::Repl { strict: true }
        );
        assert_eq!(
            parse_launch_command(&args(&["-help"])).unwrap(),
            LaunchCommand::Help
        );
        assert_eq!(
            parse_launch_command(&args(&["-version"])).unwrap(),
            LaunchCommand::Version
        );
    }

    #[test]
    fn rejects_unknown_shape() {
        assert!(parse_launch_command(&args(&["-e"])).is_err());
        assert!(parse_launch_command(&args(&["-foo", "-e", "1 = 1"])).is_err());
        assert!(parse_launch_command(&args(&["-strict", "-help"])).is_err());
    }
}
