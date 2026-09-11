use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult};
use std::path::PathBuf;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliCommand {
    Help,
    Version,
    Eval(String),
    File(PathBuf),
    Repository(PathBuf),
}

pub fn parse_cli_command(args: &[String]) -> RuntimeResult<CliCommand> {
    match args {
        [] => Ok(CliCommand::Help),
        [flag] if flag == "-help" || flag == "--help" || flag == "-h" => Ok(CliCommand::Help),
        [flag] if flag == "-version" || flag == "--version" => Ok(CliCommand::Version),
        [flag, value] if flag == "-e" && is_value(value) => Ok(CliCommand::Eval(value.clone())),
        [flag, value] if flag == "-f" && is_value(value) => {
            Ok(CliCommand::File(PathBuf::from(value)))
        }
        [flag, value] if flag == "-r" && is_value(value) => {
            Ok(CliCommand::Repository(PathBuf::from(value)))
        }
        _ => Err(RuntimeError::InvalidArguments(
            "new_pipeline supports `-e <code>`, `-f <file>`, `-r <repository>`, `-help`, `-version`"
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
        assert_eq!(command, CliCommand::Eval("1 + 1 = 2".to_string()));
    }

    #[test]
    fn parses_help_and_version() {
        assert_eq!(parse_cli_command(&args(&[])).unwrap(), CliCommand::Help);
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
