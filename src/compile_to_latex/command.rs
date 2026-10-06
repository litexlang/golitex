use super::compile::to_latex_document;
use super::source::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::knowledge_base::JsonValue;
use crate::launch_command::{parse_launch_command, LaunchCommand, OutputLanguage};
use crate::runtime::{RuntimeError, RuntimeResult};

/// Recognize a top-level -latex flag without interpreting operand strings as flags.
/// The returned boolean is artifact success, not proof verification.
pub fn run_latex_args(args: &[String]) -> Option<(String, bool)> {
    let mut selected = false;
    let mut document = false;
    let mut duplicate = false;
    let mut rest = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        if arg == "-latex" || arg == "--latex" {
            duplicate |= selected;
            selected = true;
            i += 1;
            continue;
        }
        if arg == "-document" || arg == "--document" {
            duplicate |= document;
            document = true;
            i += 1;
            continue;
        }
        rest.push(arg.clone());
        i += 1;
        if matches!(arg.as_str(), "-e" | "-f" | "-r" | "-lang" | "--lang")
            || (matches!(arg.as_str(), "-extractpython" | "-extractc")
                && !matches!(args.get(i).map(String::as_str), Some("-f" | "-r")))
        {
            if let Some(operand) = args.get(i) {
                rest.push(operand.clone());
                i += 1;
            }
        }
    }
    if !selected {
        return None;
    }
    let command = if duplicate {
        Err(RuntimeError::InvalidArguments(
            "-latex and -document may each appear only once".into(),
        ))
    } else {
        parse_launch_command(&rest)
    };
    let (language, target, path, result) = match command {
        Ok(command) => {
            let lang = command.output_language();
            let (target, path) = match &command {
                LaunchCommand::Eval { .. } => ("eval", None),
                LaunchCommand::File { path, .. } => {
                    ("file", Some(path.to_string_lossy().into_owned()))
                }
                LaunchCommand::Repository { path, .. } => {
                    ("repository", Some(path.to_string_lossy().into_owned()))
                }
                _ => ("unknown", None),
            };
            (lang, target, path, compile_command(&command))
        }
        Err(error) => (OutputLanguage::English, "unknown", None, Err(error)),
    };
    let result = result.map(|content| {
        if document {
            to_latex_document(&content, language)
        } else {
            content
        }
    });
    let success = result.is_ok();
    let (content, error) = match result {
        Ok(content) => (JsonValue::String(content), JsonValue::Null),
        Err(error) => (
            JsonValue::Null,
            JsonValue::object_from(vec![
                (
                    "kind".into(),
                    JsonValue::String("latex_conversion_error".into()),
                ),
                ("message".into(), JsonValue::String(error.to_string())),
            ]),
        ),
    };
    // Artifact keys stay stable so scripts can extract content for every locale.
    let json = JsonValue::object_from(vec![
        ("kind".into(), JsonValue::String("artifact".into())),
        ("success".into(), JsonValue::Bool(success)),
        ("artifact".into(), JsonValue::String("latex".into())),
        ("format".into(), JsonValue::String("latex".into())),
        ("target".into(), JsonValue::String(target.into())),
        (
            "path".into(),
            path.map(JsonValue::String).unwrap_or(JsonValue::Null),
        ),
        (
            "language".into(),
            JsonValue::String(language.as_str().into()),
        ),
        ("verified".into(), JsonValue::Bool(false)),
        ("content".into(), content),
        ("error".into(), error),
    ])
    .stringify_pretty();
    Some((json, success))
}
fn compile_command(command: &LaunchCommand) -> RuntimeResult<String> {
    let lang = command.output_language();
    match command {
        LaunchCommand::Eval{code,session:false,strict:false,..}=>to_latex_from_source(code,lang),
        LaunchCommand::File{path,session:false,strict:false,..}=>to_latex_from_file(&path.to_string_lossy(),lang),
        LaunchCommand::Repository{path,session:false,strict:false,..}=>to_latex_from_repository(&path.to_string_lossy(),lang),
        _=>Err(RuntimeError::InvalidArguments("-latex requires -e <code>, -f <file>, or -r <project>; -session, -strict, and executable extraction do not apply".into())),
    }
}
