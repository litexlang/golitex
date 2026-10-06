use crate::compile_to_latex::{
    to_latex_document, to_latex_from_file, to_latex_from_repository, to_latex_from_source,
};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{LatexInput, LaunchCommand, OutputLanguage};
use crate::run::run_command_outcome::CompileToLatexResult;
use crate::runtime::{RuntimeError, RuntimeResult};

/// Compile parsed source into a LaTeX artifact without execution or verification.
pub fn run_compile_to_latex(command: LaunchCommand) -> RuntimeResult<CompileToLatexResult> {
    let LaunchCommand::CompileToLatex {
        input,
        language,
        document,
    } = command
    else {
        panic!("run_compile_to_latex expects LaunchCommand::CompileToLatex");
    };
    let fragment = match &input {
        LatexInput::Code(code) => to_latex_from_source(code, language)?,
        LatexInput::File(path) => to_latex_from_file(&path.to_string_lossy(), language)?,
        LatexInput::Repository(path) => {
            to_latex_from_repository(&path.to_string_lossy(), language)?
        }
    };
    let content = if document {
        to_latex_document(&fragment, language)
    } else {
        fragment
    };
    let json = render_latex_artifact(&input, language, Some(&content), None);
    Ok(CompileToLatexResult::new(json, true))
}

/// Preserve the selected LaTeX input and locale on conversion or I/O failure.
pub fn latex_command_error_json(
    input: &LatexInput,
    language: OutputLanguage,
    error: &RuntimeError,
) -> String {
    render_latex_artifact(input, language, None, Some(error))
}

fn render_latex_artifact(
    input: &LatexInput,
    language: OutputLanguage,
    content: Option<&str>,
    error: Option<&RuntimeError>,
) -> String {
    let (target, path) = match input {
        LatexInput::Code(_) => ("eval", None),
        LatexInput::File(path) => ("file", Some(path)),
        LatexInput::Repository(path) => ("repository", Some(path)),
    };
    let error = match error {
        Some(error) => JsonValue::object_from(vec![
            (
                "kind".into(),
                JsonValue::String("latex_conversion_error".into()),
            ),
            ("message".into(), JsonValue::String(error.to_string())),
        ]),
        None => JsonValue::Null,
    };
    // Stable keys let scripts extract content regardless of the prose locale.
    JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("artifact".into())),
        ("success".into(), JsonValue::Bool(content.is_some())),
        ("artifact".into(), JsonValue::String("latex".into())),
        ("format".into(), JsonValue::String("latex".into())),
        ("target".into(), JsonValue::String(target.into())),
        (
            "path".into(),
            path.map(|path| JsonValue::String(path.to_string_lossy().into_owned()))
                .unwrap_or(JsonValue::Null),
        ),
        (
            "language".into(),
            JsonValue::String(language.as_str().into()),
        ),
        ("verified".into(), JsonValue::Bool(false)),
        (
            "content".into(),
            content
                .map(|content| JsonValue::String(content.into()))
                .unwrap_or(JsonValue::Null),
        ),
        ("error".into(), error),
    ])
    .stringify_pretty()
}
