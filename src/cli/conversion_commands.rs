use crate::prelude::*;
use crate::to_latex::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::to_python::{to_python_from_file, to_python_from_repository, to_python_from_source};
use std::fs;

pub(super) fn compile_code_to_latex(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_return(code);
    match to_latex_from_source(code.as_str(), "-latex -e") {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

pub(super) fn compile_file_to_latex(
    file_path: &str,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> String {
    if !force_isolated {
        return match to_latex_from_file(file_path) {
            Ok(s) => s,
            Err(e) => {
                let mut runtime = Runtime::new();
                runtime.output_language = output_language;
                display_runtime_error_json(&runtime, &e, true)
            }
        };
    }
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_return(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_latex_from_source(source.as_str(), file_path) {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

pub(super) fn compile_repo_to_latex(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_latex_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &error, true)
        }
    }
}

pub(super) fn compile_code_to_python(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_return(code);
    match to_python_from_source(code.as_str(), "-python -e") {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

pub(super) fn compile_file_to_python(
    file_path: &str,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> String {
    if !force_isolated {
        return match to_python_from_file(file_path) {
            Ok(s) => s,
            Err(e) => {
                let mut runtime = Runtime::new();
                runtime.output_language = output_language;
                display_runtime_error_json(&runtime, &e, true)
            }
        };
    }
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_return(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_python_from_source(source.as_str(), file_path) {
        Ok(s) => s,
        Err(e) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &e, true)
        }
    }
}

pub(super) fn compile_repo_to_python(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_python_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &error, true)
        }
    }
}
