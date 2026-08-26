use super::arguments::{read_any_value_after_flag, read_non_flag_value_after_flag};
use super::command_handlers::VERSION;
use super::messages::print_help_message;
use crate::common::helper::remove_windows_carriage_from_str;
use crate::common::output_language::OutputLanguage;
use crate::error::RuntimeError;
use crate::output::display_runtime_error_json;
use crate::pipeline::run_latex_repl;
use crate::runtime::{OutputStyle, Runtime};
use crate::to_latex::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::to_python::{to_python_from_file, to_python_from_repository, to_python_from_source};
use std::fs;
use std::process;

pub(super) fn run_latex_command(
    args: &[String],
    index: &mut usize,
    output_language: OutputLanguage,
    force_isolated: bool,
) {
    *index += 1;
    if *index >= args.len() {
        run_latex_repl(VERSION);
        return;
    }
    let target_flag = match read_any_value_after_flag(args, index, "-latex") {
        Ok(value) => value,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    let output = match target_flag.as_str() {
        "-f" => {
            let file_path = match read_non_flag_value_after_flag(args, index, "-f") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_file_to_latex(file_path.as_str(), output_language, force_isolated)
        }
        "-e" => {
            let code = match read_non_flag_value_after_flag(args, index, "-e") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_code_to_latex(code.as_str(), output_language)
        }
        "-r" => {
            let repo_path = match read_non_flag_value_after_flag(args, index, "-r") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_repo_to_latex(repo_path.as_str(), output_language)
        }
        _ => {
            eprintln!("-latex must be followed by one of: -f <file>, -e <code>, -r <repo>");
            print_help_message();
            process::exit(2);
        }
    };
    println!("{}", output);
}

pub(super) fn run_python_command(
    args: &[String],
    index: &mut usize,
    output_language: OutputLanguage,
    force_isolated: bool,
) {
    *index += 1;
    let target_flag = match read_any_value_after_flag(args, index, "-python") {
        Ok(value) => value,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    let output = match target_flag.as_str() {
        "-f" => {
            let file_path = match read_non_flag_value_after_flag(args, index, "-f") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_file_to_python(file_path.as_str(), output_language, force_isolated)
        }
        "-e" => {
            let code = match read_non_flag_value_after_flag(args, index, "-e") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_code_to_python(code.as_str(), output_language)
        }
        "-r" => {
            let repo_path = match read_non_flag_value_after_flag(args, index, "-r") {
                Ok(value) => value,
                Err(message) => {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
            };
            compile_repo_to_python(repo_path.as_str(), output_language)
        }
        _ => {
            eprintln!("-python must be followed by one of: -f <file>, -e <code>, -r <repo>");
            print_help_message();
            process::exit(2);
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
    force_isolated: bool,
) -> String {
    if !force_isolated {
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

pub(super) fn compile_code_to_python(code: &str, output_language: OutputLanguage) -> String {
    let code = remove_windows_carriage_from_str(code);
    match to_python_from_source(code.as_str(), "-python -e") {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
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
            Err(error) => render_conversion_error(output_language, &error),
        };
    }
    let source = match fs::read_to_string(file_path) {
        Ok(content) => remove_windows_carriage_from_str(&content),
        Err(e) => return format!("Could not read file {:?}: {}", file_path, e),
    };
    match to_python_from_source(source.as_str(), file_path) {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

pub(super) fn compile_repo_to_python(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_python_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn render_conversion_error(output_language: OutputLanguage, error: &RuntimeError) -> String {
    let runtime = Runtime::new(OutputStyle::Normal, false, output_language);
    display_runtime_error_json(&runtime, error, true)
}
