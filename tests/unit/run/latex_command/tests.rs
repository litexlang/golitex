use crate::knowledge_base::JsonValue;
use crate::launch_command::{
    parse_launch_command, CodeExtractionTarget, ExtractInput, LatexInput, LaunchCommand,
    OutputLanguage,
};
use crate::run::{run_command, RunCommandOutcome};
use crate::runtime::{CodeSource, Runtime};

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

    // Soft verification failure stays an ExtractExecutableCode outcome with
    // process_failed; only hard launch/runtime errors return Err.
    for target in [CodeExtractionTarget::C, CodeExtractionTarget::Python] {
        let rejected = run_command(LaunchCommand::ExtractExecutableCode {
            target,
            input: ExtractInput::Code("1 = 2".into()),
            language: OutputLanguage::English,
        })
        .unwrap();
        assert!(matches!(
            &rejected,
            RunCommandOutcome::ExtractExecutableCode(_)
        ));
        assert!(rejected.process_failed());
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
    for (input, source) in [
        (LatexInput::Code("1 = 1".into()), CodeSource::Eval),
        (
            LatexInput::File("identity.lit".into()),
            CodeSource::Real("identity.lit".into()),
        ),
        (
            LatexInput::Repository("project".into()),
            CodeSource::Real("project".into()),
        ),
    ] {
        let command = LaunchCommand::CompileToLatex {
            input,
            language: OutputLanguage::Chinese,
            document: false,
        };
        let runtime = Runtime::new(command.clone());
        assert_eq!(runtime.launch_command, command);
        assert_eq!(runtime.current_file, source);
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

#[test]
fn latex_power_bases_group_limit_integral_curl_and_factorial() {
    for (source, fragment) in [
        ("lim(a)^2=0", r"\left(\lim_"),
        ("fn_lim(f,0)^2=0", r"\left(\lim_"),
        ("limsup(a)^2=0", r"\left(\limsup_"),
        ("integral(f,0,1)^2=0", r"\left(\int_"),
        ("factorial(3)^2=0", r"\left(\left(3\right)!\right)^{2}"),
    ] {
        let latex =
            crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
        assert!(latex.contains(fragment), "{source}\n{latex}");
    }
    for (source, fragment) in [
        ("integral(fn(t R) R {integral(f,0,t)},0,1)=0", r"\xi_{1}"),
        ("sum(1,2,fn(t Z) R {sum(1,t,f)})=0", r"\iota_{1}"),
    ] {
        let latex =
            crate::compile_to_latex::to_latex_from_source(source, OutputLanguage::English).unwrap();
        assert!(latex.contains(fragment), "{source}\n{latex}");
    }
}

#[test]
fn real_function_name_containing_re_is_not_classified_as_complex() {
    let source = "have fn where(x R) R=x\nwhere(0) $in R\n";
    for target in [CodeExtractionTarget::Python, CodeExtractionTarget::C] {
        crate::extract_executable_code::extract_code_from_source(source, target).unwrap();
    }
}
