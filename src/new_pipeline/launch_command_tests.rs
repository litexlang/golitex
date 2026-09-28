use crate::new_pipeline::launch_command::{parse_launch_command, LaunchCommand};
use std::path::PathBuf;

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
