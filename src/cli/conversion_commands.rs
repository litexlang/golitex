use super::arguments::{read_any_value_after_flag, read_non_flag_value_after_flag};
use super::command_handlers::VERSION;
use super::messages::print_help_message;
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
use crate::pipeline::run_latex_repl;
use crate::runtime::{RunOptions, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;
use std::fs;
use std::process;

#[derive(Clone, Copy)]
pub(super) enum CodeExtractionCommand {
    Python,
    C,
}

pub(super) fn run_latex_command(args: &[String], index: &mut usize, options: RunOptions) {
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
            compile_file_to_latex(
                file_path.as_str(),
                options.output_language,
                options.is_isolated,
            )
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
            compile_code_to_latex(code.as_str(), options.output_language)
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
            compile_repo_to_latex(repo_path.as_str(), options.output_language)
        }
        _ => {
            eprintln!("-latex must be followed by one of: -f <file>, -e <code>, -r <repo>");
            print_help_message();
            process::exit(2);
        }
    };
    println!("{}", output);
}

pub(super) fn run_code_extraction_command(
    args: &[String],
    index: &mut usize,
    options: RunOptions,
    target: CodeExtractionCommand,
) {
    *index += 1;
    let command_flag = extraction_command_flag(target);
    let target_flag = match read_any_value_after_flag(args, index, command_flag) {
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
            compile_file_to_extracted_code(
                file_path.as_str(),
                options.output_language,
                options.is_isolated,
                target,
            )
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
            compile_repository_to_extracted_code(
                repo_path.as_str(),
                options.output_language,
                target,
            )
        }
        "-e" => {
            eprintln!(
                "{} accepts inline Litex source directly; remove `-e`",
                command_flag
            );
            print_help_message();
            process::exit(2);
        }
        code if !code.starts_with('-') => {
            compile_code_to_extracted_code(code, options.output_language, target, command_flag)
        }
        _ => {
            eprintln!(
                "{} must be followed by inline source, -f <file>, or -r <repo>",
                command_flag
            );
            print_help_message();
            process::exit(2);
        }
    };
    if *index != args.len() {
        eprintln!(
            "unexpected argument after {} target: {}",
            command_flag, args[*index]
        );
        print_help_message();
        process::exit(2);
    }
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
    target: CodeExtractionCommand,
    source_label: &str,
) -> String {
    let code = remove_windows_carriage_from_str(code);
    let result = match target {
        CodeExtractionCommand::Python => to_python_from_source(code.as_str(), source_label),
        CodeExtractionCommand::C => to_c_from_source(code.as_str(), source_label),
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
    target: CodeExtractionCommand,
) -> String {
    if !isolated {
        let result = match target {
            CodeExtractionCommand::Python => to_python_from_file(file_path),
            CodeExtractionCommand::C => to_c_from_file(file_path),
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
        CodeExtractionCommand::Python => to_python_from_source(source.as_str(), file_path),
        CodeExtractionCommand::C => to_c_from_source(source.as_str(), file_path),
    };
    match result {
        Ok(s) => s,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn compile_repository_to_extracted_code(
    repo_path: &str,
    output_language: OutputLanguage,
    target: CodeExtractionCommand,
) -> String {
    let result = match target {
        CodeExtractionCommand::Python => to_python_from_repository(repo_path),
        CodeExtractionCommand::C => to_c_from_repository(repo_path),
    };
    match result {
        Ok(output) => output,
        Err(error) => render_conversion_error(output_language, &error),
    }
}

fn extraction_command_flag(target: CodeExtractionCommand) -> &'static str {
    match target {
        CodeExtractionCommand::Python => "-extractpython",
        CodeExtractionCommand::C => "-extractc",
    }
}

fn render_conversion_error(output_language: OutputLanguage, error: &RuntimeError) -> String {
    let runtime = Runtime::new(RunOptions {
        output_language,
        ..RunOptions::default()
    });
    display_runtime_error_json(&runtime, error, true)
}
