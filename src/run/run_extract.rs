use crate::extract_executable_code::{
    to_c_from_file, to_c_from_repository, to_c_from_source, to_python_from_file,
    to_python_from_repository, to_python_from_source,
};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{CodeExtractionTarget, ExtractInput, LaunchCommand};
use crate::run::run_command_outcome::ExtractResult;
use crate::runtime::{RuntimeError, RuntimeResult};

/// `-extractpython` / `-extractc`: verify then emit extracted code artifact JSON.
pub fn run_extract(command: LaunchCommand) -> RuntimeResult<ExtractResult> {
    let LaunchCommand::Extract {
        target, input, ..
    } = &command
    else {
        panic!("run_extract expects LaunchCommand::Extract");
    };

    let (content, path, exec_target) = match input {
        ExtractInput::Code(code) => {
            let content = match target {
                CodeExtractionTarget::Python => to_python_from_source(code)?,
                CodeExtractionTarget::C => to_c_from_source(code)?,
            };
            (content, None, "eval")
        }
        ExtractInput::File(path) => {
            let path_str = path.to_string_lossy().to_string();
            let content = match target {
                CodeExtractionTarget::Python => to_python_from_file(&path_str)?,
                CodeExtractionTarget::C => to_c_from_file(&path_str)?,
            };
            (content, Some(path_str), "file")
        }
        ExtractInput::Repository(path) => {
            let path_str = path.to_string_lossy().to_string();
            let content = match target {
                CodeExtractionTarget::Python => to_python_from_repository(&path_str)?,
                CodeExtractionTarget::C => to_c_from_repository(&path_str)?,
            };
            (content, Some(path_str), "repository")
        }
    };

    let json = render_extracted_artifact(target.format_name(), exec_target, path.as_deref(), &content);
    Ok(ExtractResult::new(json, true))
}

fn render_extracted_artifact(
    format: &str,
    target: &str,
    path: Option<&str>,
    content: &str,
) -> String {
    let path_value = match path {
        Some(p) => JsonValue::String(p.to_string()),
        None => JsonValue::Null,
    };
    JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("artifact".into())),
        ("success".into(), JsonValue::Bool(true)),
        (
            "artifact".into(),
            JsonValue::String("extracted_code".into()),
        ),
        ("format".into(), JsonValue::String(format.to_string())),
        ("target".into(), JsonValue::String(target.to_string())),
        ("path".into(), path_value),
        ("output_path".into(), JsonValue::Null),
        ("content".into(), JsonValue::String(content.to_string())),
        ("error".into(), JsonValue::Null),
    ])
    .stringify_pretty()
}

pub fn extract_launch_error_json(error: &RuntimeError) -> String {
    JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("artifact".into())),
        ("success".into(), JsonValue::Bool(false)),
        (
            "artifact".into(),
            JsonValue::String("extracted_code".into()),
        ),
        ("content".into(), JsonValue::Null),
        (
            "error".into(),
            JsonValue::object_from(vec![
                ("kind".into(), JsonValue::String("extraction_error".into())),
                (
                    "message".into(),
                    JsonValue::String(format_runtime_error(error)),
                ),
            ]),
        ),
    ])
    .stringify_pretty()
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
