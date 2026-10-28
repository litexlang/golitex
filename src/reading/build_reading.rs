use crate::prelude::*;
use crate::run_module::{run_file_with_config_observed, run_project_observed};
use std::path::Path;

use super::capture::Capture;
use super::ReadingInput;

pub struct ReadingBuildResult {
    pub document: JsonValue,
    pub success: bool,
}

impl ReadingBuildResult {
    pub fn new(document: JsonValue, success: bool) -> Self {
        Self { document, success }
    }
}

pub fn build_reading(
    input: &ReadingInput,
    strict: bool,
    language: OutputLanguage,
) -> ReadingBuildResult {
    let base = match input {
        ReadingInput::File(path) => path
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new(".")),
        ReadingInput::Project(path) => path.as_path(),
        ReadingInput::Source(_) | ReadingInput::Empty => Path::new("."),
    };
    let mut capture = Capture::new(base, language);
    if let ReadingInput::File(path) = input {
        capture.set_entry_file(path);
    }
    let run = match input {
        ReadingInput::File(path) => run_file_with_config_observed(
            LaunchCommand::File {
                path: path.clone(),
                session: false,
                strict,
                language,
            },
            &mut capture,
        )
        .map(|result| {
            (
                result.run.success,
                result.run.session_error.map(|error| error.to_string()),
            )
        }),
        ReadingInput::Project(path) => run_project_observed(
            LaunchCommand::Repository {
                path: path.clone(),
                session: false,
                strict,
                language,
            },
            &mut capture,
        )
        .map(|result| {
            (
                result.run.success,
                result.run.session_error.map(|error| error.to_string()),
            )
        }),
        ReadingInput::Source(code) => {
            let mut runtime = Runtime::new_with_result_detail(
                LaunchCommand::Eval {
                    code: code.clone(),
                    session: false,
                    strict,
                    language,
                },
                crate::result_detail::OutputDetail::Detailed,
            );
            runtime
                .run_litex_code_observed(code, &mut capture)
                .map(|result| {
                    (
                        result.success,
                        result.session_error.map(|error| error.to_string()),
                    )
                })
        }
        ReadingInput::Empty => Ok((true, None)),
    };
    let (success, error) = match run {
        Ok(result) => result,
        Err(error) => (false, Some(error.to_string())),
    };
    ReadingBuildResult::new(capture.finish(success, error, strict), success)
}
