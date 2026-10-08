use crate::prelude::*;
use crate::run::{run_command, RunCommandOutcome};
use crate::runtime::{CodeSource, RealOrVirtualPath};

fn parse(args: &[&str]) -> RuntimeResult<LaunchCommand> {
    parse_launch_command(&args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>())
}

#[test]
fn lean_command_preserves_launch_options_and_file_provenance() {
    for args in [
        vec!["-strict", "-lean", "-lang", "zh", "-f", "identity.lit"],
        vec!["-f", "identity.lit", "-lang", "zh", "-lean", "-strict"],
    ] {
        let command = parse(&args).unwrap();
        assert_eq!(
            command,
            LaunchCommand::CompileToLean {
                path: "identity.lit".into(),
                strict: true,
                language: OutputLanguage::Chinese,
            }
        );
        assert!(command.is_strict());
        assert_eq!(command.output_language(), OutputLanguage::Chinese);
        let runtime = Runtime::new(command.clone());
        assert_eq!(runtime.launch_command, command);
        assert_eq!(runtime.code_source, CodeSource::StandaloneFile);
        assert_eq!(
            runtime.current_file,
            RealOrVirtualPath::Real("identity.lit".into())
        );
    }
}

#[test]
fn lean_requires_one_standalone_file_and_no_other_output_mode() {
    for args in [
        vec!["-lean"],
        vec!["-lean", "-f"],
        vec!["-lean", "-f", ""],
        vec!["-lean", "-f", "identity.lit", "-lean"],
        vec!["-lean", "-f", "identity.lit", "-session"],
        vec!["-lean", "-e", "1 = 1"],
        vec!["-lean", "-r", "project"],
        vec!["-lean", "-latex", "-f", "identity.lit"],
        vec!["-lean", "-document", "-f", "identity.lit"],
        vec!["-lean", "-extractc", "1 = 1"],
    ] {
        assert!(
            matches!(parse(&args), Err(RuntimeError::InvalidArguments(_))),
            "{args:?}"
        );
    }
}

#[test]
fn lean_spelling_in_an_operand_is_not_a_mode() {
    assert!(
        matches!(parse(&["-f", "-lean"]).unwrap(), LaunchCommand::File { path, .. } if path == std::path::Path::new("-lean"))
    );
    assert!(
        matches!(parse(&["-e", "-lean"]).unwrap(), LaunchCommand::Eval { code, .. } if code == "-lean")
    );
    assert!(matches!(
        parse(&["-extractpython", "-lean"]).unwrap(),
        LaunchCommand::ExtractExecutableCode { .. }
    ));
    assert!(
        matches!(parse(&["-lean", "-f", "-lean"]).unwrap(), LaunchCommand::CompileToLean { path, .. } if path == std::path::Path::new("-lean"))
    );
}

#[test]
fn lean_dispatch_returns_a_complete_artifact_or_an_error() {
    let path = "lean/examples/one_equals_itself/statement.lit";
    let command = parse(&["-lean", "-strict", "-f", path]).unwrap();
    let outcome = run_command(command).unwrap();
    assert!(!outcome.process_failed());
    assert!(outcome.normal_json().is_none());
    let RunCommandOutcome::CompileToLean(result) = outcome else {
        panic!("Lean outcome");
    };
    assert_eq!(
        result.source,
        std::fs::read_to_string("lean/examples/one_equals_itself/statement.lean").unwrap()
    );

    let command = parse(&[
        "-lean",
        "-f",
        "tests/fixtures/compile_to_lean/failed_fact.lit",
    ])
    .unwrap();
    let error = match run_command(command) {
        Err(error) => error,
        Ok(_) => panic!("failed verification must return an error"),
    };
    assert_eq!(
        error,
        RuntimeError::Unsupported("phase=verify: statement 1 failed Litex verification".into())
    );
}
