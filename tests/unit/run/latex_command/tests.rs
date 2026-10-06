use crate::knowledge_base::JsonValue;
use crate::launch_command::{
    parse_launch_command, CodeExtractionTarget, ExtractInput, LatexInput, LaunchCommand,
    OutputLanguage,
};
use crate::run::{run_command, RunCommandOutcome};
use crate::runtime::{CodeSource, RealOrVirtualPath, Runtime};

#[test]
fn latex_dispatch_is_parse_only_and_has_its_own_result() {
    let command = parse_launch_command(&["-latex".into(), "-e".into(), "1 = 2".into()]).unwrap();
    let outcome = run_command(command).unwrap();
    assert!(!outcome.process_failed());
    assert!(matches!(&outcome, RunCommandOutcome::CompileToLatex(_)));
    let json = JsonValue::parse(outcome.normal_json().unwrap()).unwrap();
    let fields = json.as_object().unwrap();
    assert_eq!(
        fields.get("artifact"),
        Some(&JsonValue::String("latex".into()))
    );
    assert_eq!(fields.get("verified"), Some(&JsonValue::Bool(false)));
    assert!(fields
        .get("content")
        .unwrap()
        .as_str()
        .unwrap()
        .contains("1 = 2"));

    // The identical false fact must still fail executable extraction's verification.
    for target in [CodeExtractionTarget::C, CodeExtractionTarget::Python] {
        assert!(run_command(LaunchCommand::ExtractExecutableCode {
            target,
            input: ExtractInput::Code("1 = 2".into()),
            language: OutputLanguage::English,
        })
        .is_err());
        let outcome = run_command(LaunchCommand::ExtractExecutableCode {
            target,
            input: ExtractInput::Code("have a R = 1".into()),
            language: OutputLanguage::English,
        })
        .unwrap();
        assert!(matches!(
            &outcome,
            RunCommandOutcome::ExtractExecutableCode(_)
        ));
        assert!(!outcome.process_failed());
    }
}

#[test]
fn latex_runtime_provenance_tracks_each_input_kind() {
    for (input, source, file) in [
        (
            LatexInput::Code("1 = 1".into()),
            CodeSource::Eval,
            RealOrVirtualPath::Eval,
        ),
        (
            LatexInput::File("identity.lit".into()),
            CodeSource::StandaloneFile,
            RealOrVirtualPath::Real("identity.lit".into()),
        ),
        (
            LatexInput::Repository("project".into()),
            CodeSource::StandaloneFile,
            RealOrVirtualPath::Real("project".into()),
        ),
    ] {
        let command = LaunchCommand::CompileToLatex {
            input,
            language: OutputLanguage::Chinese,
            document: false,
        };
        let runtime = Runtime::new(command.clone());
        assert_eq!(runtime.launch_command, command);
        assert_eq!(runtime.code_source, source);
        assert_eq!(runtime.current_file, file);
        assert_eq!(runtime.execution_environments_stack.len(), 1);
        assert_eq!(runtime.parse_scope_stack.len(), 1);
    }
}

#[test]
fn document_option_changes_wrapping_only() {
    let mut contents = Vec::new();
    for document in [false, true] {
        let outcome = run_command(LaunchCommand::CompileToLatex {
            input: LatexInput::Code("1 = 2".into()),
            language: OutputLanguage::Chinese,
            document,
        })
        .unwrap();
        let json = JsonValue::parse(outcome.normal_json().unwrap()).unwrap();
        contents.push(
            json.as_object()
                .unwrap()
                .get("content")
                .unwrap()
                .as_str()
                .unwrap()
                .to_string(),
        );
    }
    assert!(!contents[0].contains(r"\begin{document}"));
    assert_eq!(
        contents[1],
        crate::compile_to_latex::to_latex_document(&contents[0], OutputLanguage::Chinese)
    );
}
