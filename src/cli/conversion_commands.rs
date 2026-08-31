use super::command::ExtractionKind;
use crate::error::RuntimeError;
use crate::extract_code_of_other_languages_from_litex::c::{
    to_c_from_file, to_c_from_repository, to_c_from_source,
};
use crate::extract_code_of_other_languages_from_litex::python::{
    to_python_from_file, to_python_from_repository, to_python_from_source,
};
use crate::latex_renderer::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::output::display_runtime_error_json;
use crate::output::language::OutputLanguage;
use crate::runtime::{ExecutionOption, RunOptions, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;
use std::fs;

pub(super) fn run_latex_command(target: &str, options: RunOptions) {
    let output = match options.execution() {
        ExecutionOption::File | ExecutionOption::IsolatedFile => {
            compile_file_to_latex(target, options.output_language(), options.is_isolated())
        }
        ExecutionOption::Eval => compile_code_to_latex(target, options.output_language()),
        ExecutionOption::Repo => compile_repo_to_latex(target, options.output_language()),
        ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
            unreachable!("LaTeX command was resolved to an unsupported target")
        }
    };
    println!("{}", output);
}

pub(super) fn run_code_extraction_command(
    source: &str,
    options: RunOptions,
    target: ExtractionKind,
) {
    let command_flag = extraction_command_flag(target);
    let output = match options.execution() {
        ExecutionOption::File | ExecutionOption::IsolatedFile => compile_file_to_extracted_code(
            source,
            options.output_language(),
            options.is_isolated(),
            target,
        ),
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
    println!("{}", output);
}

pub(super) fn compile_code_to_latex(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_from_str(code);
    match to_latex_from_source(code.as_str(), "-latex -e") {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

pub(super) fn compile_file_to_latex(
    file_path: &str,
    output_language: OutputLanguage,
    isolated: bool,
) -> String {
    if !isolated {
        return match to_latex_from_file(file_path) {
            Ok(s) => s,
            Err(error) => render_conversion_error(output_language, &error),
        };
    }
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_from_str(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_latex_from_source(source.as_str(), file_path) {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

pub(super) fn compile_repo_to_latex(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_latex_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn compile_code_to_extracted_code(
    code: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
    source_label: &str,
) -> String {
    let code = remove_windows_carriage_from_str(code);
    let result = match target {
        ExtractionKind::Python => to_python_from_source(code.as_str(), source_label),
        ExtractionKind::C => to_c_from_source(code.as_str(), source_label),
    };
    match result {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn compile_file_to_extracted_code(
    file_path: &str,
    output_language: OutputLanguage,
    isolated: bool,
    target: ExtractionKind,
) -> String {
    if !isolated {
        let result = match target {
            ExtractionKind::Python => to_python_from_file(file_path),
            ExtractionKind::C => to_c_from_file(file_path),
        };
        return match result {
            Ok(s) => s,
            Err(error) => render_conversion_error(output_language, &error),
        };
    }
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_from_str(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    let result = match target {
        ExtractionKind::Python => to_python_from_source(source.as_str(), file_path),
        ExtractionKind::C => to_c_from_source(source.as_str(), file_path),
    };
    match result {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn compile_repository_to_extracted_code(
    repo_path: &str,
    output_language: OutputLanguage,
    target: ExtractionKind,
) -> String {
    let result = match target {
        ExtractionKind::Python => to_python_from_repository(repo_path),
        ExtractionKind::C => to_c_from_repository(repo_path),
    };
    match result {
        Ok(output) => output,
        Err(error) => render_conversion_error(output_language, &error),
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
    display_runtime_error_json(&runtime, error, true)
}
