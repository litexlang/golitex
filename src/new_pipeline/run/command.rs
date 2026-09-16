use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult};
use std::path::PathBuf;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliCommand {
    Help,
    Version,
    Repl,
    Eval { code: String, session: bool },
    File { path: PathBuf, session: bool },
    Repository { path: PathBuf, session: bool },
}

pub fn parse_cli_command(args: &[String]) -> RuntimeResult<CliCommand> {
    let mut session = false;
    let mut rest = Vec::new();
    for arg in args {
        if arg == "-session" || arg == "--session" {
            session = true;
        } else {
            rest.push(arg.clone());
        }
    }

    match rest.as_slice() {
        [] => Ok(CliCommand::Repl),
        [flag] if flag == "-help" || flag == "--help" || flag == "-h" => Ok(CliCommand::Help),
        [flag] if flag == "-version" || flag == "--version" => Ok(CliCommand::Version),
        [flag, value] if flag == "-e" && is_value(value) => Ok(CliCommand::Eval {
            code: value.clone(),
            session,
        }),
        [flag, value] if flag == "-f" && is_value(value) => Ok(CliCommand::File {
            path: PathBuf::from(value),
            session,
        }),
        [flag, value] if flag == "-r" && is_value(value) => Ok(CliCommand::Repository {
            path: PathBuf::from(value),
            session,
        }),
        _ => Err(RuntimeError::InvalidArguments(
            "new_pipeline supports bare REPL, `-e <code>`, `-f <file>`, `-r <repository>`, optional `-session`, `-help`, `-version`"
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
        let command = parse_cli_command(&args(&["-e", "1 + 1 = 2"])).unwrap();
        assert_eq!(
            command,
            CliCommand::Eval {
                code: "1 + 1 = 2".to_string(),
                session: false,
            }
        );
    }

    #[test]
    fn parses_session_with_file_either_order() {
        assert_eq!(
            parse_cli_command(&args(&["-f", "a.lit", "-session"])).unwrap(),
            CliCommand::File {
                path: PathBuf::from("a.lit"),
                session: true,
            }
        );
        assert_eq!(
            parse_cli_command(&args(&["-session", "-f", "a.lit"])).unwrap(),
            CliCommand::File {
                path: PathBuf::from("a.lit"),
                session: true,
            }
        );
    }

    #[test]
    fn parses_help_version_and_repl() {
        assert_eq!(parse_cli_command(&args(&[])).unwrap(), CliCommand::Repl);
        assert_eq!(
            parse_cli_command(&args(&["-session"])).unwrap(),
            CliCommand::Repl
        );
        assert_eq!(
            parse_cli_command(&args(&["-help"])).unwrap(),
            CliCommand::Help
        );
        assert_eq!(
            parse_cli_command(&args(&["-version"])).unwrap(),
            CliCommand::Version
        );
    }

    #[test]
    fn rejects_unknown_shape() {
        assert!(parse_cli_command(&args(&["-e"])).is_err());
        assert!(parse_cli_command(&args(&["-strict", "-e", "1 = 1"])).is_err());
    }
}
