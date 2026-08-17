use crate::litex_to_lean_compiler::{
    compile_litex_file_to_lean, compile_markdown_ledger_file_to_lean,
};
use crate::prelude::*;
use crate::to_latex::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::to_python::{to_python_from_file, to_python_from_repository, to_python_from_source};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
const DETAIL_FLAG: &str = "-detail";
const COMPACT_FLAG: &str = "-compact";
const STRICT_FLAG: &str = "-strict";
const LANGUAGE_FLAG: &str = "-lang";
const SUMMARIZE_FLAG: &str = "-summarize";
const ISOLATED_FLAG: &str = "-isolated";
const TRUST_BEFORE_LINE_FLAG: &str = "-trust-before-line";

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let detail_output = remove_flag(&mut args, DETAIL_FLAG);
    let compact_output = remove_flag(&mut args, COMPACT_FLAG);
    if detail_output && compact_output {
        eprintln!("-compact and -detail cannot be used together");
        print_help_message();
        process::exit(2);
    }
    let output_style = if compact_output {
        OutputStyle::Compact
    } else if detail_output {
        OutputStyle::Detailed
    } else {
        OutputStyle::Normal
    };
    let strict_mode = remove_flag(&mut args, STRICT_FLAG);
    let summarize_output = remove_flag(&mut args, SUMMARIZE_FLAG);
    let force_isolated = remove_flag(&mut args, ISOLATED_FLAG);
    let output_language = match remove_language_flag(&mut args) {
        Ok(language) => language,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    let trust_before_line = match remove_trust_before_line_flag(&mut args) {
        Ok(value) => value,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    if let Err(message) =
        validate_trust_before_line_invocation(&args, strict_mode, trust_before_line)
    {
        eprintln!("{}", message);
        print_help_message();
        process::exit(2);
    }
    let mut index: usize = 0;

    if !args.is_empty() {
        let head = args[index].as_str();

        match head {
            "-help" => {
                print_help_message();
                println!();
                println!("If no options are provided, starts interactive REPL mode.");
                return;
            }
            "-version" => {
                println!("Litex Kernel: litex {}", VERSION);
                return;
            }
            "-upgrade" => {
                println!("{}", upgrade_message(VERSION));
                return;
            }
            "-e" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("-e");
                runtime.set_output_style(output_style);
                runtime.strict_mode = strict_mode;
                runtime.output_language = output_language;

                let (stmt_results, runtime_error) = run_source_code(code.as_str(), &mut runtime);
                let mut output =
                    render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
                if summarize_output {
                    output.1.push('\n');
                    output.1.push_str(
                        display_run_summary_json_with_runtime(
                            &runtime,
                            &stmt_results,
                            &runtime_error,
                        )
                        .as_str(),
                    );
                    output.1.push('\n');
                }
                println!("{}", output.1.trim());
                return;
            }
            "-f" => {
                index += 1;
                let file_path = match read_non_flag_value_after_flag(&args, &mut index, "-f") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                main_flag_file(
                    file_path.as_str(),
                    output_style,
                    strict_mode,
                    output_language,
                    summarize_output,
                    force_isolated,
                    trust_before_line,
                );
                return;
            }
            "-r" => {
                index += 1;
                let repo_path = match read_non_flag_value_after_flag(&args, &mut index, "-r") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                main_flag_repo(
                    repo_path.as_str(),
                    output_style,
                    strict_mode,
                    output_language,
                    summarize_output,
                );
                return;
            }
            "-runner" => {
                index += 1;
                let (ok, output) = match main_flag_runner(
                    &args,
                    &mut index,
                    output_style,
                    strict_mode,
                    output_language,
                    force_isolated,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-graph" => {
                index += 1;
                let (ok, output, save_path) = match main_flag_graph(
                    &args,
                    &mut index,
                    output_style,
                    strict_mode,
                    output_language,
                    force_isolated,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let trimmed_output = string_with_trimmed_outer_newlines(output.as_str());
                if let Some(save_path) = save_path {
                    let path = Path::new(save_path.as_str());
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            if let Err(error) = fs::create_dir_all(parent) {
                                eprintln!(
                                    "failed to create graph output directory for {}: {}",
                                    save_path, error
                                );
                                process::exit(1);
                            }
                        }
                    }
                    if let Err(error) = fs::write(path, format!("{}\n", trimmed_output)) {
                        eprintln!("failed to write graph JSON to {}: {}", save_path, error);
                        process::exit(1);
                    }
                    println!("saved graph JSON to {}", save_path);
                } else {
                    println!("{}", trimmed_output);
                }
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-factgraph" => {
                index += 1;
                let (ok, output, save_path) = match main_flag_fact_graph(
                    &args,
                    &mut index,
                    output_style,
                    strict_mode,
                    output_language,
                    force_isolated,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let trimmed_output = string_with_trimmed_outer_newlines(output.as_str());
                if let Some(save_path) = save_path {
                    let path = Path::new(save_path.as_str());
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            if let Err(error) = fs::create_dir_all(parent) {
                                eprintln!(
                                    "failed to create fact graph output directory for {}: {}",
                                    save_path, error
                                );
                                process::exit(1);
                            }
                        }
                    }
                    if let Err(error) = fs::write(path, format!("{}\n", trimmed_output)) {
                        eprintln!(
                            "failed to write fact graph JSON to {}: {}",
                            save_path, error
                        );
                        process::exit(1);
                    }
                    println!("saved fact graph JSON to {}", save_path);
                } else {
                    println!("{}", trimmed_output);
                }
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-defgraph" => {
                index += 1;
                let (ok, output, save_path) = match main_flag_definition_graph(
                    &args,
                    &mut index,
                    output_style,
                    strict_mode,
                    output_language,
                    force_isolated,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let trimmed_output = string_with_trimmed_outer_newlines(output.as_str());
                if let Some(save_path) = save_path {
                    let path = Path::new(save_path.as_str());
                    if let Some(parent) = path.parent() {
                        if !parent.as_os_str().is_empty() {
                            if let Err(error) = fs::create_dir_all(parent) {
                                eprintln!(
                                    "failed to create definition graph output directory for {}: {}",
                                    save_path, error
                                );
                                process::exit(1);
                            }
                        }
                    }
                    if let Err(error) = fs::write(path, format!("{}\n", trimmed_output)) {
                        eprintln!(
                            "failed to write definition graph JSON to {}: {}",
                            save_path, error
                        );
                        process::exit(1);
                    }
                    println!("saved definition graph JSON to {}", save_path);
                } else {
                    println!("{}", trimmed_output);
                }
                if !ok {
                    process::exit(1);
                }
                return;
            }
            "-session" => {
                index += 1;
                let preload = match read_session_preload(&args, &mut index) {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                if let Err(message) = validate_session_preload(force_isolated, &preload) {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
                run_session_with_output_style_and_strict_and_language_and_preload(
                    output_style,
                    strict_mode,
                    output_language,
                    force_isolated,
                    preload,
                );
                return;
            }
            "-lean-ledger" => {
                index += 1;
                let ledger_path =
                    match read_non_flag_value_after_flag(&args, &mut index, "-lean-ledger") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                let output_path =
                    match read_non_flag_value_after_flag(&args, &mut index, "-lean-ledger") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("-lean-ledger requires an output .lean path: {}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                if let Some(unexpected) = args.get(index) {
                    eprintln!(
                        "unexpected argument after -lean-ledger output: {}",
                        unexpected
                    );
                    print_help_message();
                    process::exit(2);
                }
                match compile_markdown_ledger_file_to_lean(
                    Path::new(&ledger_path),
                    Path::new(&output_path),
                ) {
                    Ok(count) => {
                        println!(
                            "wrote {} freshly generated Lean entries to {}",
                            count, output_path
                        );
                    }
                    Err(message) => {
                        eprintln!("{}", message);
                        process::exit(1);
                    }
                }
                return;
            }
            "-lean" => {
                index += 1;
                let source_path = match read_non_flag_value_after_flag(&args, &mut index, "-lean") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let output_path = match read_non_flag_value_after_flag(&args, &mut index, "-lean") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("-lean requires an output .lean path: {}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                if let Some(unexpected) = args.get(index) {
                    eprintln!("unexpected argument after -lean output: {}", unexpected);
                    print_help_message();
                    process::exit(2);
                }
                match compile_litex_file_to_lean(Path::new(&source_path), Path::new(&output_path)) {
                    Ok(()) => println!("wrote freshly generated Lean to {}", output_path),
                    Err(message) => {
                        eprintln!("{}", message);
                        process::exit(1);
                    }
                }
                return;
            }
            "-latex" => {
                index += 1;
                if index >= args.len() {
                    run_latex_repl(VERSION);
                    return;
                }
                let latex_target_flag = match read_any_value_after_flag(&args, &mut index, "-latex")
                {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                let latex_output_result = match latex_target_flag.as_str() {
                    "-f" => {
                        let file_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-f") {
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
                        let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
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
                        let repo_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-r") {
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
                        eprintln!(
                            "-latex must be followed by one of: -f <file>, -e <code>, -r <repo>"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", latex_output_result);
                return;
            }
            "-python" => {
                index += 1;
                let python_target_flag =
                    match read_any_value_after_flag(&args, &mut index, "-python") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                let python_output_result = match python_target_flag.as_str() {
                    "-f" => {
                        let file_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-f") {
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
                        let code = match read_non_flag_value_after_flag(&args, &mut index, "-e") {
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
                        let repo_path =
                            match read_non_flag_value_after_flag(&args, &mut index, "-r") {
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
                        eprintln!(
                            "-python must be followed by one of: -f <file>, -e <code>, -r <repo>"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", python_output_result);
                return;
            }
            "-fmt" => {
                index += 1;
                let code = match read_non_flag_value_after_flag(&args, &mut index, "-fmt") {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", format_code(code.as_str()));
                return;
            }
            "-install" => {
                index += 1;
                let module_name =
                    match read_non_flag_value_after_flag(&args, &mut index, "-install") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                install_module(module_name.as_str());
                return;
            }
            "-uninstall" => {
                index += 1;
                let module_name =
                    match read_non_flag_value_after_flag(&args, &mut index, "-uninstall") {
                        Ok(value) => value,
                        Err(message) => {
                            eprintln!("{}", message);
                            print_help_message();
                            process::exit(2);
                        }
                    };
                uninstall_module(module_name.as_str());
                return;
            }
            "-list" => {
                list_installed_modules();
                return;
            }
            "-update" => {
                index += 1;
                let module_name = match read_non_flag_value_after_flag(&args, &mut index, "-update")
                {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                update_module(module_name.as_str());
                return;
            }
            "-tutorial" => {
                run_tutorial();
                return;
            }
            other => {
                eprintln!("unknown argument: {}", other);
                print_help_message();
                process::exit(2);
            }
        }
    }

    run_repl_with_output_style_and_strict_and_language_and_isolation(
        VERSION,
        output_style,
        strict_mode,
        output_language,
        force_isolated,
    );
}

fn remove_flag(args: &mut Vec<String>, flag_name: &str) -> bool {
    let before_len = args.len();
    args.retain(|arg| arg != flag_name);
    args.len() != before_len
}

fn remove_trust_before_line_flag(args: &mut Vec<String>) -> Result<Option<usize>, String> {
    let flag_count = args
        .iter()
        .filter(|arg| arg.as_str() == TRUST_BEFORE_LINE_FLAG)
        .count();
    if flag_count == 0 {
        return Ok(None);
    }
    if flag_count > 1 {
        return Err(format!(
            "{} may be provided only once",
            TRUST_BEFORE_LINE_FLAG
        ));
    }

    let flag_index = args
        .iter()
        .position(|arg| arg == TRUST_BEFORE_LINE_FLAG)
        .expect("the trust-before-line flag count was already checked");
    let Some(value) = args.get(flag_index + 1) else {
        return Err(format!(
            "{} requires a positive ASCII decimal line number",
            TRUST_BEFORE_LINE_FLAG
        ));
    };
    if value.is_empty() || !value.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "{} requires a positive ASCII decimal line number, got {}",
            TRUST_BEFORE_LINE_FLAG, value
        ));
    }
    let line = value.parse::<usize>().map_err(|_| {
        format!(
            "{} line number exceeds the supported range: {}",
            TRUST_BEFORE_LINE_FLAG, value
        )
    })?;
    if line == 0 {
        return Err(format!(
            "{} requires a line number greater than 0",
            TRUST_BEFORE_LINE_FLAG
        ));
    }

    args.remove(flag_index + 1);
    args.remove(flag_index);
    Ok(Some(line))
}

fn validate_trust_before_line_invocation(
    args: &[String],
    strict_mode: bool,
    trust_before_line: Option<usize>,
) -> Result<(), String> {
    if trust_before_line.is_none() {
        return Ok(());
    }
    if strict_mode {
        return Err(format!(
            "{} cannot be used with {}",
            TRUST_BEFORE_LINE_FLAG, STRICT_FLAG
        ));
    }
    if args.len() != 2 || args.first().map(String::as_str) != Some("-f") {
        return Err(format!(
            "{} is supported only with a direct -f <file> or -isolated -f <file> command and does not accept additional arguments",
            TRUST_BEFORE_LINE_FLAG
        ));
    }
    if args
        .get(1)
        .map(|file| file.is_empty() || file.starts_with('-'))
        .unwrap_or(true)
    {
        return Err(format!(
            "{} requires a direct -f <file> target",
            TRUST_BEFORE_LINE_FLAG
        ));
    }
    Ok(())
}

fn remove_language_flag(args: &mut Vec<String>) -> Result<OutputLanguage, String> {
    let Some(flag_index) = args.iter().position(|arg| arg == LANGUAGE_FLAG) else {
        return Ok(OutputLanguage::English);
    };

    if flag_index + 1 >= args.len() {
        return Err(format!(
            "{} requires a value: {}",
            LANGUAGE_FLAG,
            OutputLanguage::supported_codes_text()
        ));
    }

    let value = args.remove(flag_index + 1);
    args.remove(flag_index);
    OutputLanguage::from_cli_lang(value.as_str())
}

/// `index` must point at the first token after the flag; reads one value and advances past it.
fn read_non_flag_value_after_flag(
    args: &[String],
    index: &mut usize,
    flag_name: &str,
) -> Result<String, String> {
    let value = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => candidate.clone(),
        _ => {
            return Err(format!("{} requires a value", flag_name));
        }
    };
    *index += 1;
    Ok(value)
}

/// `index` must point at the first token after the flag; reads one token (can be another flag) and advances past it.
fn read_any_value_after_flag(
    args: &[String],
    index: &mut usize,
    flag_name: &str,
) -> Result<String, String> {
    let value = match args.get(*index) {
        Some(candidate) => candidate.clone(),
        None => return Err(format!("{} requires a value", flag_name)),
    };
    *index += 1;
    Ok(value)
}

fn read_session_preload(args: &[String], index: &mut usize) -> Result<SessionPreload, String> {
    if *index == args.len() {
        return Ok(SessionPreload::None);
    }
    let flag = args.get(*index).map(String::as_str).unwrap_or_default();
    *index += 1;
    let file = match flag {
        "-f" => read_non_flag_value_after_flag(args, index, "-f")?,
        "-before" => read_non_flag_value_after_flag(args, index, "-before")?,
        _ => {
            return Err(
                "-session accepts only an optional -f <file> or -before <file> target".to_string(),
            )
        }
    };
    if *index != args.len() {
        return Err(format!(
            "-session {} <file> does not accept additional arguments",
            flag
        ));
    }
    match flag {
        "-f" => Ok(SessionPreload::ThroughFile(file)),
        "-before" => Ok(SessionPreload::BeforeFile(file)),
        _ => unreachable!("session preload flag was already validated"),
    }
}

fn validate_session_preload(force_isolated: bool, preload: &SessionPreload) -> Result<(), String> {
    if force_isolated && matches!(preload, SessionPreload::BeforeFile(_)) {
        return Err(
            "-isolated cannot be used with -session -before; the target must be a registered project file"
                .to_string(),
        );
    }
    Ok(())
}

fn print_help_message() {
    println!("{}", help_message());
}

fn remove_windows_carriage_return(path_or_code: &str) -> String {
    path_or_code.replace('\r', "")
}

fn main_flag_file(
    file_flag: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
    force_isolated: bool,
    trust_before_line: Option<usize>,
) {
    let path = remove_windows_carriage_return(file_flag);

    let abs_file_path: PathBuf = if Path::new(path.as_str()).is_absolute() {
        PathBuf::from(path.as_str())
    } else {
        let working_directory_result = env::current_dir();
        let working_directory = match working_directory_result {
            Ok(path) => path,
            Err(error) => {
                eprintln!("Error: failed to get current working directory: {}", error);
                return;
            }
        };
        working_directory.join(path.as_str())
    };

    if abs_file_path.parent().is_none() {
        eprintln!("Error: could not get parent directory of file path");
        return;
    }

    let path_string = match abs_file_path.to_str() {
        Some(path_string) => path_string.to_string(),
        None => {
            eprintln!("Error: file path is not valid UTF-8");
            return;
        }
    };

    let mut runtime = Runtime::new();
    runtime.set_output_style(output_style);
    runtime.strict_mode = strict_mode;
    runtime.output_language = output_language;
    let (stmt_results, runtime_error) = run_file_with_project_context_and_trusted_prefix(
        path_string.as_str(),
        &mut runtime,
        force_isolated,
        trust_before_line,
    );
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if let Some(report) = runtime.trusted_prefix_report.as_ref() {
        let mut trusted_prefix_output = display_trusted_prefix_report_json(report);
        if !output.trim().is_empty() {
            trusted_prefix_output.push('\n');
            trusted_prefix_output.push_str(output.trim());
        }
        output = trusted_prefix_output;
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime_and_trusted_prefix(
                &runtime,
                &stmt_results,
                &runtime_error,
                report,
            )
            .as_str(),
        );
        output.push('\n');
    } else if summarize_output {
        output.push('\n');
        output.push_str(
            display_run_summary_json_with_runtime(&runtime, &stmt_results, &runtime_error).as_str(),
        );
        output.push('\n');
    }
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
    if runtime.trusted_prefix_setup_error.is_some() {
        process::exit(2);
    }
    if ok && runtime.isolated && trust_before_line.is_none() {
        run_isolated_repl_with_runtime(VERSION, &mut runtime);
    }
}

fn main_flag_repo(
    repo_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
) {
    let path = remove_windows_carriage_return(repo_path);
    let output = run_source_code_in_repository_for_cli_with_output_style_and_summary_and_language(
        path.as_str(),
        output_style,
        strict_mode,
        output_language,
        summarize_output,
    );
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
}

fn main_flag_runner(
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String), String> {
    let target_flag = read_any_value_after_flag(args, index, "-runner")?;
    let hide_file_paths = !output_style.is_detailed();
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let output = if strict_mode {
                run_runner_for_code_strict_with_language(
                    code.as_str(),
                    "-runner -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_runner_for_code_with_language(
                    code.as_str(),
                    "-runner -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok(output)
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            Ok(run_runner_for_file_with_strict_language_and_isolation(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            ))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            Ok(run_runner_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            ))
        }
        _ => Err("-runner must be followed by one of: -f <file>, -e <code>, -r <repo>".to_string()),
    }
}

fn main_flag_graph(
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String, Option<String>), String> {
    let target_flag = read_any_value_after_flag(args, index, "-graph")?;
    let hide_file_paths = !output_style.is_detailed();
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = if strict_mode {
                run_graph_for_code_strict_with_language(
                    code.as_str(),
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_graph_for_code_with_language(
                    code.as_str(),
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok((output.0, output.1, save_path))
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = run_graph_for_file_with_strict_language_and_isolation(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            );
            Ok((output.0, output.1, save_path))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            let save_path = read_optional_graph_save_path(args, index)?;
            let output = run_graph_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            );
            Ok((output.0, output.1, save_path))
        }
        _ => Err(
            "-graph must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]"
                .to_string(),
        ),
    }
}

fn main_flag_fact_graph(
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String, Option<String>), String> {
    let target_flag = read_any_value_after_flag(args, index, "-factgraph")?;
    let hide_file_paths = !output_style.is_detailed();
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let save_path = read_optional_fact_graph_save_path(args, index)?;
            let output = if strict_mode {
                run_fact_graph_for_code_strict_with_language(
                    code.as_str(),
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_fact_graph_for_code_with_language(
                    code.as_str(),
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok((output.0, output.1, save_path))
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            let save_path = read_optional_fact_graph_save_path(args, index)?;
            let output = run_fact_graph_for_file_with_strict_language_and_isolation(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            );
            Ok((output.0, output.1, save_path))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            let save_path = read_optional_fact_graph_save_path(args, index)?;
            let output = run_fact_graph_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            );
            Ok((output.0, output.1, save_path))
        }
        _ => Err(
            "-factgraph must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]"
                .to_string(),
        ),
    }
}

fn main_flag_definition_graph(
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String, Option<String>), String> {
    let target_flag = read_any_value_after_flag(args, index, "-defgraph")?;
    let hide_file_paths = !output_style.is_detailed();
    match target_flag.as_str() {
        "-e" => {
            let code = read_non_flag_value_after_flag(args, index, "-e")?;
            let save_path = read_optional_definition_graph_save_path(args, index)?;
            let output = if strict_mode {
                run_definition_graph_for_code_strict_with_language(
                    code.as_str(),
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_definition_graph_for_code_with_language(
                    code.as_str(),
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            };
            Ok((output.0, output.1, save_path))
        }
        "-f" => {
            let file_path = read_non_flag_value_after_flag(args, index, "-f")?;
            let save_path = read_optional_definition_graph_save_path(args, index)?;
            let output = run_definition_graph_for_file_with_strict_language_and_isolation(
                file_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            );
            Ok((output.0, output.1, save_path))
        }
        "-r" => {
            let repo_path = read_non_flag_value_after_flag(args, index, "-r")?;
            let save_path = read_optional_definition_graph_save_path(args, index)?;
            let output = run_definition_graph_for_repo_with_strict_and_language(
                repo_path.as_str(),
                hide_file_paths,
                strict_mode,
                output_language,
            );
            Ok((output.0, output.1, save_path))
        }
        _ => Err(
            "-defgraph must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]"
                .to_string(),
        ),
    }
}

fn read_optional_graph_save_path(
    args: &[String],
    index: &mut usize,
) -> Result<Option<String>, String> {
    let save_path = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => {
            *index += 1;
            Some(candidate.clone())
        }
        _ => None,
    };

    if let Some(unexpected) = args.get(*index) {
        return Err(format!(
            "unexpected argument after -graph target: {}",
            unexpected
        ));
    }

    Ok(save_path)
}

fn read_optional_fact_graph_save_path(
    args: &[String],
    index: &mut usize,
) -> Result<Option<String>, String> {
    let save_path = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => {
            *index += 1;
            Some(candidate.clone())
        }
        _ => None,
    };

    if let Some(unexpected) = args.get(*index) {
        return Err(format!(
            "unexpected argument after -factgraph target: {}",
            unexpected
        ));
    }

    Ok(save_path)
}

fn read_optional_definition_graph_save_path(
    args: &[String],
    index: &mut usize,
) -> Result<Option<String>, String> {
    let save_path = match args.get(*index) {
        Some(candidate) if !candidate.starts_with('-') => {
            *index += 1;
            Some(candidate.clone())
        }
        _ => None,
    };

    if let Some(unexpected) = args.get(*index) {
        return Err(format!(
            "unexpected argument after -defgraph target: {}",
            unexpected
        ));
    }

    Ok(save_path)
}

fn string_with_trimmed_outer_newlines(text: &str) -> String {
    text.trim().to_string()
}

fn compile_code_to_latex(code: &str, output_language: OutputLanguage) -> String {
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

fn compile_file_to_latex(
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

fn compile_repo_to_latex(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_latex_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &error, true)
        }
    }
}

fn compile_code_to_python(code: &str, output_language: OutputLanguage) -> String {
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

fn compile_file_to_python(
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

fn compile_repo_to_python(repo_path: &str, output_language: OutputLanguage) -> String {
    match to_python_from_repository(repo_path) {
        Ok(output) => output,
        Err(error) => {
            let mut runtime = Runtime::new();
            runtime.output_language = output_language;
            display_runtime_error_json(&runtime, &error, true)
        }
    }
}

fn format_code(_code: &str) -> String {
    return "-fmt: format code is not implemented in the Rust kernel yet".to_string();
}

fn install_module(module_name: &str) -> String {
    return format!(
        "-install: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn uninstall_module(module_name: &str) -> String {
    return format!(
        "-uninstall: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn list_installed_modules() -> String {
    return "-list: module manager is not implemented in the Rust kernel yet".to_string();
}

fn update_module(module_name: &str) -> String {
    return format!(
        "-update: module manager is not implemented in the Rust kernel yet (module: {})",
        module_name
    );
}

fn run_tutorial() -> String {
    return "-tutorial: not implemented in the Rust kernel yet".to_string();
}

/// Print instructions instead of running a package manager.
/// Litex can be installed by Homebrew, release packages, or source builds, so
/// startup should not perform network or system changes on the user's machine.
fn upgrade_message(version: &str) -> String {
    let mut result = format!("Litex version {}\n\nUpgrade Litex:\n", version);

    if cfg!(target_os = "macos") {
        result.push_str("macOS with Homebrew:\n");
        result.push_str("  brew update\n");
        result.push_str("  brew upgrade litexlang/tap/litex\n\n");
    } else if cfg!(target_os = "linux") {
        result.push_str("Linux with the .deb release package:\n");
        result.push_str(
            "  Download the latest litex_<tag>_amd64.deb from GitHub Releases and run:\n",
        );
        result.push_str("  sudo dpkg -i litex_<tag>_amd64.deb\n\n");
    } else if cfg!(target_os = "windows") {
        result.push_str("Windows release zip install:\n");
        result.push_str("  Rerun the PowerShell install command from docs/Setup.md.\n\n");
    } else {
        result.push_str("Open the latest GitHub Release and install the package for your OS.\n\n");
    }

    result.push_str("Release page: https://github.com/litexlang/golitex/releases/latest\n");
    result.push_str("Full setup notes: https://litexlang.com/doc/Setup");
    result
}

fn help_message() -> String {
    let result = r#"litex : start an isolated persistent REPL; terminal import is available
litex -f <file> : require a direct-parent litex.config and run the module prefix through this file
litex -isolated -f <file> : run any standalone file and continue in an isolated REPL
litex -f <file> -trust-before-line <X> : trust top-level statements before the exact header line X, then verify from X
litex -r <folder> : run a module's recursive [export] tree, or the root prefix through a selected submodule
litex -e <code> : execute the given code
litex -runner -f <file> : run a file and return one wrapper JSON object
litex -runner -e <code> : run source code and return one wrapper JSON object
litex -runner -r <project> : run a project and return one wrapper JSON object
litex -session : run a machine-readable project REPL for framed code blocks
litex -session -f <file> : load the project prefix through a registered file, then keep the same Runtime in session mode
litex -session -before <file> : load the registered project prefix before a file, then edit in that file's Runtime context
litex -lean <input.lit> <output.lean> : compile one Litex file into one complete Lean file
litex -lean-ledger <markdown> <output.lean> : freshly compile every H2 Litex fence into one namespaced Lean file
litex -graph -f <file> <json> : run a file and save a prop/function/fact relation graph JSON object
litex -graph -e <code> <json> : run source code and save a prop/function/fact relation graph JSON object
litex -graph -r <project> <json> : run a project and save a prop/function/fact relation graph JSON object
litex -factgraph -f <file> <json> : run a file and save a fact-only verification dependency graph JSON object
litex -factgraph -e <code> <json> : run source code and save a fact-only verification dependency graph JSON object
litex -factgraph -r <project> <json> : run a project and save a fact-only verification dependency graph JSON object
litex -defgraph -f <file> <json> : run a file and save an environment-backed definition dependency graph JSON object
litex -defgraph -e <code> <json> : run source code and save an environment-backed definition dependency graph JSON object
litex -defgraph -r <project> <json> : run a project and save an environment-backed definition dependency graph JSON object
litex -latex : run Litex interactively and print LaTeX output in your terminal
litex -latex -f <file> : compile the given file to LaTeX
litex -latex -e <code> : compile the given code to LaTeX
litex -latex -r <project> : compile the given project to LaTeX
litex -python -f <file> : run the frozen experimental Python extractor on a file
litex -python -e <code> : run the frozen experimental Python extractor on source code
litex -python -r <project> : run the frozen experimental Python extractor on a recursive project
litex -help : show the help message
litex -version : show the version
litex -upgrade : show upgrade instructions for this platform
litex -compact : show minimal success output; RuntimeError output always uses full detailed diagnostics
litex : show normal success output with internal statements and direct verification reasons; RuntimeError output is detailed
litex -detail : include full audit trace details and raw source paths for both success and RuntimeError JSON output
litex -strict : verify configured imports and -f prefix entries, and reject user trust, trust have, and axiom statements
litex -trust-before-line <X> : preview development tool for direct -f runs; X must name an exact top-level statement header line, cannot be used with -strict, and an isolated cutoff run exits after its summary
litex -summarize : append one run summary JSON object after ordinary verifier command output
litex -lang <en|zh|zh-Hans|ja|ko|es|fr|de|pt|ru|ar|hi|vi|id> : choose output language
litex -fmt : format the given code
litex -install <module> : install the given module
litex -uninstall <module> : uninstall the given module
litex -list : list all installed modules
litex -update <module> : update the given module
litex -tutorial : run the tutorial
"#;
    result.to_string()
}

#[cfg(test)]
mod tests {
    use super::{
        help_message, read_session_preload, remove_trust_before_line_flag, upgrade_message,
        validate_session_preload, validate_trust_before_line_invocation,
    };
    use crate::prelude::SessionPreload;

    #[test]
    fn help_lists_upgrade_command() {
        let message = help_message();
        assert!(message.contains("litex -upgrade"));
    }

    #[test]
    fn help_lists_strict_command() {
        let message = help_message();
        assert!(message.contains("litex -strict"));
    }

    #[test]
    fn help_lists_summarize_command() {
        let message = help_message();
        assert!(message.contains("litex -summarize"));
    }

    #[test]
    fn help_lists_compact_output() {
        let message = help_message();
        assert!(message.contains("litex -compact"));
        assert!(message.contains("RuntimeError output always uses full detailed diagnostics"));
    }

    #[test]
    fn help_lists_trust_before_line_command() {
        let message = help_message();
        assert!(message.contains("litex -f <file> -trust-before-line <X>"));
        assert!(message.contains("exact top-level statement header line"));
        assert!(message.contains("cannot be used with -strict"));
    }

    #[test]
    fn trust_before_line_accepts_a_positive_ascii_decimal() {
        let mut args = vec![
            "-trust-before-line".to_string(),
            "420".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
        ];

        let line = remove_trust_before_line_flag(&mut args).expect("a positive line should parse");

        assert_eq!(line, Some(420));
        assert_eq!(args, vec!["-f".to_string(), "chapter.lit".to_string()]);
    }

    #[test]
    fn trust_before_line_accepts_the_flag_after_the_file_target() {
        let mut args = vec![
            "-f".to_string(),
            "chapter.lit".to_string(),
            "-trust-before-line".to_string(),
            "420".to_string(),
        ];

        let line = remove_trust_before_line_flag(&mut args)
            .expect("the global flag may follow the primary command");

        assert_eq!(line, Some(420));
        assert_eq!(args, vec!["-f".to_string(), "chapter.lit".to_string()]);
    }

    #[test]
    fn trust_before_line_rejects_a_missing_value() {
        let mut args = vec![
            "-f".to_string(),
            "chapter.lit".to_string(),
            "-trust-before-line".to_string(),
        ];

        let error =
            remove_trust_before_line_flag(&mut args).expect_err("the flag requires a value");

        assert!(error.contains("requires a positive ASCII decimal line number"));
    }

    #[test]
    fn trust_before_line_rejects_zero_negative_and_non_ascii_decimal_values() {
        for value in ["0", "-1", "+1", "1.5", "１２"] {
            let mut args = vec!["-trust-before-line".to_string(), value.to_string()];

            let error = remove_trust_before_line_flag(&mut args)
                .expect_err("only a positive ASCII decimal should parse");

            assert!(
                error.contains("positive ASCII decimal") || error.contains("greater than 0"),
                "unexpected error for {value}: {error}"
            );
        }
    }

    #[test]
    fn trust_before_line_rejects_overflow() {
        let overflow = format!("{}0", usize::MAX);
        let mut args = vec!["-trust-before-line".to_string(), overflow];

        let error =
            remove_trust_before_line_flag(&mut args).expect_err("overflow should be rejected");

        assert!(error.contains("exceeds the supported range"));
    }

    #[test]
    fn trust_before_line_rejects_duplicate_flags() {
        let mut args = vec![
            "-trust-before-line".to_string(),
            "10".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
            "-trust-before-line".to_string(),
            "20".to_string(),
        ];

        let error =
            remove_trust_before_line_flag(&mut args).expect_err("the flag must not be repeated");

        assert!(error.contains("may be provided only once"));
    }

    #[test]
    fn trust_before_line_accepts_only_an_exact_direct_file_command() {
        let file_args = vec!["-f".to_string(), "chapter.lit".to_string()];
        assert!(validate_trust_before_line_invocation(&file_args, false, Some(420)).is_ok());

        for args in [
            vec!["-r".to_string(), "Demo".to_string()],
            vec!["-e".to_string(), "1 = 1".to_string()],
            vec!["-session".to_string()],
            vec![
                "-runner".to_string(),
                "-f".to_string(),
                "chapter.lit".to_string(),
            ],
            vec![
                "-graph".to_string(),
                "-f".to_string(),
                "chapter.lit".to_string(),
                "graph.json".to_string(),
            ],
            vec![
                "-python".to_string(),
                "-f".to_string(),
                "chapter.lit".to_string(),
            ],
            vec![
                "-latex".to_string(),
                "-f".to_string(),
                "chapter.lit".to_string(),
            ],
            vec![
                "-f".to_string(),
                "chapter.lit".to_string(),
                "extra".to_string(),
            ],
            vec!["-f".to_string(), "-session".to_string()],
        ] {
            let error = validate_trust_before_line_invocation(&args, false, Some(420))
                .expect_err("only exact direct file commands should be accepted");
            assert!(
                error.contains("supported only") || error.contains("direct -f <file> target"),
                "unexpected error for {args:?}: {error}"
            );
        }
    }

    #[test]
    fn trust_before_line_rejects_strict_mode() {
        let args = vec!["-f".to_string(), "chapter.lit".to_string()];

        let error = validate_trust_before_line_invocation(&args, true, Some(420))
            .expect_err("strict and trusted-prefix execution are incompatible");

        assert!(error.contains("cannot be used with -strict"));
    }

    #[test]
    fn trust_before_line_validation_does_not_change_flagless_commands() {
        let args = vec![
            "-runner".to_string(),
            "-f".to_string(),
            "chapter.lit".to_string(),
        ];

        assert!(validate_trust_before_line_invocation(&args, true, None).is_ok());
    }

    #[test]
    fn help_lists_session_command() {
        let message = help_message();
        assert!(message.contains("litex -session"));
        assert!(message.contains("litex -session -f <file>"));
        assert!(message.contains("litex -session -before <file>"));
    }

    #[test]
    fn session_accepts_an_optional_file_preload() {
        let args = vec![
            "-session".to_string(),
            "-f".to_string(),
            "chap4.lit".to_string(),
        ];
        let mut index = 1;

        let preload = read_session_preload(args.as_slice(), &mut index)
            .expect("session file target should parse");

        assert_eq!(
            preload,
            SessionPreload::ThroughFile("chap4.lit".to_string())
        );
        assert_eq!(index, args.len());
    }

    #[test]
    fn session_accepts_a_before_file_preload() {
        let args = vec![
            "-session".to_string(),
            "-before".to_string(),
            "chap5.lit".to_string(),
        ];
        let mut index = 1;

        let preload = read_session_preload(args.as_slice(), &mut index)
            .expect("session before target should parse");

        assert_eq!(preload, SessionPreload::BeforeFile("chap5.lit".to_string()));
        assert_eq!(index, args.len());
    }

    #[test]
    fn session_rejects_non_file_targets() {
        let args = vec!["-session".to_string(), "-r".to_string(), "Demo".to_string()];
        let mut index = 1;

        let error = read_session_preload(args.as_slice(), &mut index)
            .expect_err("session repository target should be rejected");

        assert!(error.contains("-f <file> or -before <file>"));
    }

    #[test]
    fn session_rejects_combined_preload_targets() {
        let args = vec![
            "-session".to_string(),
            "-before".to_string(),
            "chap5.lit".to_string(),
            "-f".to_string(),
            "chap4.lit".to_string(),
        ];
        let mut index = 1;

        let error = read_session_preload(args.as_slice(), &mut index)
            .expect_err("session preload targets must be mutually exclusive");

        assert!(error.contains("does not accept additional arguments"));
    }

    #[test]
    fn session_rejects_a_missing_before_file() {
        let args = vec!["-session".to_string(), "-before".to_string()];
        let mut index = 1;

        let error = read_session_preload(args.as_slice(), &mut index)
            .expect_err("a before target requires a file");

        assert!(error.contains("-before requires a value"));
    }

    #[test]
    fn session_rejects_isolated_before_target() {
        let preload = SessionPreload::BeforeFile("chap5.lit".to_string());

        let error = validate_session_preload(true, &preload)
            .expect_err("a before target requires project discovery");

        assert!(error.contains("-isolated cannot be used with -session -before"));
        assert!(validate_session_preload(false, &preload).is_ok());
    }

    #[test]
    fn help_lists_python_command() {
        let message = help_message();
        assert!(message.contains("litex -python -f <file>"));
    }

    #[test]
    fn help_lists_lean_ledger_command() {
        let message = help_message();
        assert!(message.contains("litex -lean <input.lit> <output.lean>"));
        assert!(message.contains("litex -lean-ledger <markdown> <output.lean>"));
    }

    #[test]
    fn help_lists_graph_command() {
        let message = help_message();
        assert!(message.contains("litex -graph -f <file> <json>"));
    }

    #[test]
    fn help_lists_fact_graph_command() {
        let message = help_message();
        assert!(message.contains("litex -factgraph -f <file> <json>"));
    }

    #[test]
    fn help_lists_definition_graph_command() {
        let message = help_message();
        assert!(message.contains("litex -defgraph -f <file> <json>"));
    }

    #[test]
    fn help_explains_project_file_and_run_plan_modes() {
        let message = help_message();
        assert!(message.contains("module prefix through this file"));
        assert!(message.contains("litex -isolated -f <file>"));
        assert!(message.contains("recursive [export] tree"));
        assert!(message.contains("selected submodule"));
    }

    #[test]
    fn upgrade_message_mentions_version_and_release_page() {
        let message = upgrade_message("test-version");
        assert!(message.contains("Litex version test-version"));
        assert!(message.contains("https://github.com/litexlang/golitex/releases/latest"));
    }
}
