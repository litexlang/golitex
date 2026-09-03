use super::command::ExtractionKind;
use super::json_output::{execution_target, render_artifact, simple_error};
use crate::error::RuntimeError;
use crate::extract_code_of_other_languages_from_litex::c::{
    to_c_from_file, to_c_from_repository, to_c_from_source,
};
use crate::extract_code_of_other_languages_from_litex::python::{
    to_python_from_file, to_python_from_repository, to_python_from_source,
};
use crate::latex_renderer::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::output::language::OutputLanguage;
use crate::output::render_runtime_error_json;
use crate::pipeline::file_execution::file_execution_option;
use crate::prelude::{render_json_value, JsonValue};
use crate::runtime::{ExecutionOption, RunOptions, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;
use std::fs;

pub(super) fn run_latex_command(target: &str, options: RunOptions) -> bool {
    let result = match options.execution() {
        ExecutionOption::File => match file_execution_option(target) {
            ExecutionOption::File => compile_file_to_latex(target, options.output_language()),
            ExecutionOption::IsolatedFile => {
                compile_isolated_file_to_latex(target, options.output_language())
            }
            _ => unreachable!("file context resolved to a non-file execution option"),
        },
        ExecutionOption::IsolatedFile => {
            compile_isolated_file_to_latex(target, options.output_language())
        }
        ExecutionOption::Eval => compile_code_to_latex(target, options.output_language()),
        ExecutionOption::Repo => compile_repo_to_latex(target, options.output_language()),
        ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
            unreachable!("LaTeX command was resolved to an unsupported target")
        }
    };
    print_conversion_result("rendered_source", "latex", target, options, result)
}

pub(super) fn run_code_extraction_command(
    source: &str,
    options: RunOptions,
    target: ExtractionKind,
) -> bool {
    let command_flag = extraction_command_flag(target);
    let result = match options.execution() {
        ExecutionOption::File => match file_execution_option(source) {
            ExecutionOption::File => {
                compile_file_to_extracted_code(source, options.output_language(), target)
            }
            ExecutionOption::IsolatedFile => {
                compile_isolated_file_to_extracted_code(source, options.output_language(), target)
            }
            _ => unreachable!("file context resolved to a non-file execution option"),
        },
        ExecutionOption::IsolatedFile => {
            compile_isolated_file_to_extracted_code(source, options.output_language(), target)
        }
        ExecutionOption::Repo => {
            compile_repository_to_extracted_code(source, options.output_language(), target)
        }
        ExecutionOption::Eval => {
            compile_code_to_extracted_code(source, options.output_language(), target, command_flag)
        }
        ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
            unreachable!("extraction command was resolved to an unsupported target")
        }
    };
    let format = match target {
        ExtractionKind::Python => "python",
        ExtractionKind::C => "c",
    };
    print_conversion_result("extracted_code", format, source, options, result)
}

pub(super) fn compile_code_to_latex(
    code: &str,
    output_language: OutputLanguage,
) -> Result<String, String> {
    let code = remove_windows_carriage_from_str(code);
    match to_latex_from_source(code.as_str(), "-latex -e") {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

pub(super) fn compile_file_to_latex(
    file_path: &str,
    output_language: OutputLanguage,
) -> Result<String, String> {
    match to_latex_from_file(file_path) {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

pub(super) fn compile_isolated_file_to_latex(
    file_path: &str,
    output_language: OutputLanguage,
) -> Result<String, String> {
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_from_str(&content),
        Err(error) => {
            return Err(render_json_value(
                &simple_error(
                    "file_read_error",
                    format!("Could not read file {:?}: {}", file_path, error).as_str(),
                ),
                0,
            ));
        }
    };
    match to_latex_from_source(source.as_str(), file_path) {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

pub(super) fn compile_repo_to_latex(
    repo_path: &str,
    output_language: OutputLanguage,
) -> Result<String, String> {
    match to_latex_from_repository(repo_path) {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

fn compile_code_to_extracted_code(
    code: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
    source_label: &str,
) -> Result<String, String> {
    let code = remove_windows_carriage_from_str(code);
    let result = match target {
        ExtractionKind::Python => to_python_from_source(code.as_str(), source_label),
        ExtractionKind::C => to_c_from_source(code.as_str(), source_label),
    };
    match result {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

fn compile_file_to_extracted_code(
    file_path: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
) -> Result<String, String> {
    let result = match target {
        ExtractionKind::Python => to_python_from_file(file_path),
        ExtractionKind::C => to_c_from_file(file_path),
    };
    match result {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

fn compile_isolated_file_to_extracted_code(
    file_path: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
) -> Result<String, String> {
    compile_file_to_extracted_code(file_path, output_language, target)
}

fn compile_repository_to_extracted_code(
    repo_path: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
) -> Result<String, String> {
    let result = match target {
        ExtractionKind::Python => to_python_from_repository(repo_path),
        ExtractionKind::C => to_c_from_repository(repo_path),
    };
    match result {
        Ok(output) => Ok(output),
        Err(error) => Err(render_conversion_error(output_language, &error)),
    }
}

fn extraction_command_flag(target: ExtractionKind) -> &'static str {
    match target {
        ExtractionKind::Python => "-extractpython",
        ExtractionKind::C => "-extractc",
    }
}

fn render_conversion_error(output_language: OutputLanguage, error: &RuntimeError) -> String {
    let runtime = Runtime::new(RunOptions::default().with_output_language(output_language));
    render_runtime_error_json(&runtime, error, true)
}

fn print_conversion_result(
    artifact: &str,
    format: &str,
    input: &str,
    options: RunOptions,
    result: Result<String, String>,
) -> bool {
    let (target, has_path) = execution_target(options);
    let path = has_path.then_some(input);
    let (content, error) = match result {
        Ok(content) => (JsonValue::JsonString(content), JsonValue::Null),
        Err(error) => (JsonValue::Null, JsonValue::RawJson(error)),
    };
    let ok = matches!(error, JsonValue::Null);
    println!(
        "{}",
        render_artifact(artifact, format, target, path, None, content, error,)
    );
    ok
}
