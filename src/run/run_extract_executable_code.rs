use crate::extract_executable_code::{
    to_c_from_file, to_c_from_repository, to_c_from_source, to_python_from_file,
    to_python_from_repository, to_python_from_source,
};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{CodeExtractionTarget, ExtractInput, LaunchCommand, OutputLanguage};
use crate::run::run_command_outcome::ExtractExecutableCodeResult;
use crate::runtime::{RuntimeError, RuntimeResult};

/// `-extractpython` / `-extractc`: verify then emit extracted code artifact JSON.
pub fn run_extract_executable_code(
    command: LaunchCommand,
) -> RuntimeResult<ExtractExecutableCodeResult> {
    let LaunchCommand::ExtractExecutableCode { target, input, .. } = &command else {
        return Err(RuntimeError::InvalidArguments(
            "run_extract_executable_code expects LaunchCommand::ExtractExecutableCode".to_string(),
        ));
    };

    let language = command.output_language();
    let extract_once = || -> RuntimeResult<(String, Option<String>, &'static str)> {
        match input {
            ExtractInput::Code(code) => {
                let content = match target {
                    CodeExtractionTarget::Python => to_python_from_source(code)?,
                    CodeExtractionTarget::C => to_c_from_source(code)?,
                };
                Ok((content, None, "eval"))
            }
            ExtractInput::File(path) => {
                let path_str = path.to_string_lossy().to_string();
                let content = match target {
                    CodeExtractionTarget::Python => to_python_from_file(&path_str)?,
                    CodeExtractionTarget::C => to_c_from_file(&path_str)?,
                };
                Ok((content, Some(path_str), "file"))
            }
            ExtractInput::Repository(path) => {
                let path_str = path.to_string_lossy().to_string();
                let content = match target {
                    CodeExtractionTarget::Python => to_python_from_repository(&path_str)?,
                    CodeExtractionTarget::C => to_c_from_repository(&path_str)?,
                };
                Ok((content, Some(path_str), "repository"))
            }
        }
    };

    match extract_once() {
        Ok((content, path, exec_target)) => {
            let json = render_extracted_artifact(
                Some(target.format_name()),
                Some(exec_target),
                path.as_deref(),
                language,
                Some(&content),
                None,
            );
            Ok(ExtractExecutableCodeResult::new(json, true))
        }
        Err(error) if is_extract_soft_fail(&error) => {
            let (exec_target, path) = match input {
                ExtractInput::Code(_) => ("eval", None),
                ExtractInput::File(path) => ("file", Some(path.to_string_lossy().into_owned())),
                ExtractInput::Repository(path) => {
                    ("repository", Some(path.to_string_lossy().into_owned()))
                }
            };
            let json = render_extracted_artifact(
                Some(target.format_name()),
                Some(exec_target),
                path.as_deref(),
                language,
                None,
                Some(&error),
            );
            Ok(ExtractExecutableCodeResult::new(json, false))
        }
        Err(error) => Err(error),
    }
}

fn is_extract_soft_fail(error: &RuntimeError) -> bool {
    matches!(error, RuntimeError::Unsupported(message) if message.starts_with("soft_fail:"))
}

fn render_extracted_artifact(
    format: Option<&str>,
    target: Option<&str>,
    path: Option<&str>,
    language: OutputLanguage,
    content: Option<&str>,
    error: Option<&RuntimeError>,
) -> String {
    let key = |name| crate::json_output::json_keys::localize_key(name, language);
    let optional_string = |value: Option<&str>| {
        value
            .map(|s| JsonValue::String(s.to_string()))
            .unwrap_or(JsonValue::Null)
    };
    let error_value = error
        .map(|error| {
            JsonValue::object_from(vec![
                (key("kind"), JsonValue::String("extraction_error".into())),
                (
                    key("message"),
                    JsonValue::String(format_runtime_error(error)),
                ),
            ])
        })
        .unwrap_or(JsonValue::Null);
    JsonValue::object_from(vec![
        (key("kind"), JsonValue::String("artifact".into())),
        (
            key("artifact_result"),
            crate::json_output::helper::artifact_result_value(error.is_none()),
        ),
        (key("artifact"), JsonValue::String("extracted_code".into())),
        (key("format"), optional_string(format)),
        (key("target"), optional_string(target)),
        (key("path"), optional_string(path)),
        (key("output_path"), JsonValue::Null),
        (key("language"), JsonValue::String(language.as_str().into())),
        (key("content"), optional_string(content)),
        (key("error"), error_value),
    ])
    .stringify_pretty()
}

pub fn extract_launch_error_json(error: &RuntimeError) -> String {
    render_extracted_artifact(None, None, None, OutputLanguage::English, None, Some(error))
}

/// Retain the selected extraction command even when input loading fails.
pub fn extract_command_error_json(
    target: &CodeExtractionTarget,
    input: &ExtractInput,
    language: OutputLanguage,
    error: &RuntimeError,
) -> String {
    let (exec_target, path) = match input {
        ExtractInput::Code(_) => ("eval", None),
        ExtractInput::File(path) => ("file", Some(path.to_string_lossy().into_owned())),
        ExtractInput::Repository(path) => ("repository", Some(path.to_string_lossy().into_owned())),
    };
    render_extracted_artifact(
        Some(target.format_name()),
        Some(exec_target),
        path.as_deref(),
        language,
        None,
        Some(error),
    )
}

fn format_runtime_error(error: &RuntimeError) -> String {
    match error {
        RuntimeError::InvalidArguments(message) => message.clone(),
        RuntimeError::Io { path, message } => {
            format!("{}: {}", path.display(), message)
        }
        RuntimeError::ParseError(error) => {
            format!("{} at line {} in {}", error.message, error.line, error.path)
        }
        RuntimeError::Unsupported(message) => message.clone(),
        RuntimeError::InternalBug(_) => error.to_string(),
    }
}
