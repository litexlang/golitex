use super::arguments::{
    parse_global_options, read_any_value_after_flag, read_non_flag_value_after_flag,
    read_session_preload, validate_session_preload, CliOptions,
};
use crate::pipeline::{run_repository, RunOutputOptions};
use crate::prelude::*;
use crate::stmt_result_to_lean_compiler::{
    compile_litex_file_to_lean_file, compile_litex_markdown_code_blocks_to_lean_file,
};
use crate::to_latex::{to_latex_from_file, to_latex_from_repository, to_latex_from_source};
use crate::to_python::{to_python_from_file, to_python_from_repository, to_python_from_source};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Clone, Copy)]
enum GraphKind {
    Result,
    Fact,
    Definition,
}

impl GraphKind {
    fn flag(self) -> &'static str {
        match self {
            Self::Result => "-graph",
            Self::Fact => "-factgraph",
            Self::Definition => "-defgraph",
        }
    }

    fn output_name(self) -> &'static str {
        match self {
            Self::Result => "graph",
            Self::Fact => "fact graph",
            Self::Definition => "definition graph",
        }
    }
}

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let CliOptions {
        output_style,
        strict_mode,
        summarize_output,
        force_isolated,
        output_language,
        trust_before_line,
    } = match parse_global_options(&mut args) {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
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
                if args.get(index).is_some_and(|arg| arg == "-lean") {
                    index += 1;
                    let output_path =
                        match read_non_flag_value_after_flag(&args, &mut index, "-lean") {
                            Ok(value) => value,
                            Err(message) => {
                                eprintln!("-lean requires an output .lean path: {}", message);
                                print_help_message();
                                process::exit(2);
                            }
                        };
                    if !force_isolated {
                        eprintln!(
                            "single-file Litex-to-Lean requires `-isolated`: litex -f <input.lit> -isolated -lean <output.lean>"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                    if strict_mode
                        || summarize_output
                        || output_style != OutputStyle::Normal
                        || trust_before_line.is_some()
                    {
                        eprintln!(
                            "single-file Litex-to-Lean accepts only `-f <input.lit> -isolated -lean <output.lean>`"
                        );
                        print_help_message();
                        process::exit(2);
                    }
                    if let Some(unexpected) = args.get(index) {
                        eprintln!("unexpected argument after -lean output: {}", unexpected);
                        print_help_message();
                        process::exit(2);
                    }
                    match compile_litex_file_to_lean_file(
                        Path::new(&file_path),
                        Path::new(&output_path),
                    ) {
                        Ok(()) => println!("wrote freshly generated Lean to {}", output_path),
                        Err(message) => {
                            eprintln!("{}", message);
                            process::exit(1);
                        }
                    }
                    return;
                }
                run_file_command(
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
                run_repository_command(
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
                let (ok, output) = match run_runner_command(
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
            "-graph" | "-factgraph" | "-defgraph" => {
                let graph_kind = match head {
                    "-graph" => GraphKind::Result,
                    "-factgraph" => GraphKind::Fact,
                    "-defgraph" => GraphKind::Definition,
                    _ => unreachable!("graph command was already matched"),
                };
                index += 1;
                let (ok, output, save_path) = match run_graph_command(
                    graph_kind,
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
                if let Err(message) =
                    print_or_save_graph_output(graph_kind, &output, save_path.as_deref())
                {
                    eprintln!("{}", message);
                    process::exit(1);
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
                let markdown_path =
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
                match compile_litex_markdown_code_blocks_to_lean_file(
                    Path::new(&markdown_path),
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

fn print_help_message() {
    println!("{}", help_message());
}

fn run_file_command(
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
    let (stmt_results, runtime_error, trusted_prefix_report, trusted_prefix_setup_rejected) =
        run_file_with_project_context_and_trusted_prefix(
            path_string.as_str(),
            &mut runtime,
            force_isolated,
            trust_before_line,
        );
    let (ok, mut output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, true);
    if let Some(report) = trusted_prefix_report.as_ref() {
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
    if trusted_prefix_setup_rejected {
        process::exit(2);
    }
    if ok && runtime.current_source_allows_inline_imports() && trust_before_line.is_none() {
        run_isolated_repl_with_runtime(VERSION, &mut runtime);
    }
}

fn run_repository_command(
    repo_path: &str,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    summarize_output: bool,
) {
    let path = remove_windows_carriage_return(repo_path);
    let (_, output) = run_repository(
        path.as_str(),
        RunOutputOptions {
            output_style,
            strict_mode,
            output_language,
            summarize: summarize_output,
        },
    );
    println!("{}", string_with_trimmed_outer_newlines(output.as_str()));
}

fn run_runner_command(
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

fn run_graph_command(
    graph_kind: GraphKind,
    args: &[String],
    index: &mut usize,
    output_style: OutputStyle,
    strict_mode: bool,
    output_language: OutputLanguage,
    force_isolated: bool,
) -> Result<(bool, String, Option<String>), String> {
    let command_flag = graph_kind.flag();
    let target_flag = read_any_value_after_flag(args, index, command_flag)?;
    let target = match target_flag.as_str() {
        "-e" | "-f" | "-r" => read_non_flag_value_after_flag(args, index, target_flag.as_str())?,
        _ => {
            return Err(format!(
                "{} must be followed by one of: -f <file> [json], -e <code> [json], -r <repo> [json]",
                command_flag
            ));
        }
    };
    let save_path = read_optional_graph_save_path(args, index, command_flag)?;
    let hide_file_paths = !output_style.is_detailed();
    let output = match (graph_kind, target_flag.as_str()) {
        (GraphKind::Result, "-e") => {
            if strict_mode {
                run_graph_for_code_strict_with_language(
                    &target,
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_graph_for_code_with_language(
                    &target,
                    "-graph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Fact, "-e") => {
            if strict_mode {
                run_fact_graph_for_code_strict_with_language(
                    &target,
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_fact_graph_for_code_with_language(
                    &target,
                    "-factgraph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Definition, "-e") => {
            if strict_mode {
                run_definition_graph_for_code_strict_with_language(
                    &target,
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            } else {
                run_definition_graph_for_code_with_language(
                    &target,
                    "-defgraph -e",
                    hide_file_paths,
                    output_language,
                )
            }
        }
        (GraphKind::Result, "-f") => run_graph_for_file_with_strict_language_and_isolation(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
            force_isolated,
        ),
        (GraphKind::Fact, "-f") => run_fact_graph_for_file_with_strict_language_and_isolation(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
            force_isolated,
        ),
        (GraphKind::Definition, "-f") => {
            run_definition_graph_for_file_with_strict_language_and_isolation(
                &target,
                hide_file_paths,
                strict_mode,
                output_language,
                force_isolated,
            )
        }
        (GraphKind::Result, "-r") => run_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        (GraphKind::Fact, "-r") => run_fact_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        (GraphKind::Definition, "-r") => run_definition_graph_for_repo_with_strict_and_language(
            &target,
            hide_file_paths,
            strict_mode,
            output_language,
        ),
        _ => unreachable!("graph target flag was already validated"),
    };

    Ok((output.0, output.1, save_path))
}

fn read_optional_graph_save_path(
    args: &[String],
    index: &mut usize,
    command_flag: &str,
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
            "unexpected argument after {} target: {}",
            command_flag, unexpected
        ));
    }

    Ok(save_path)
}

fn print_or_save_graph_output(
    graph_kind: GraphKind,
    output: &str,
    save_path: Option<&str>,
) -> Result<(), String> {
    let trimmed_output = string_with_trimmed_outer_newlines(output);
    let Some(save_path) = save_path else {
        println!("{}", trimmed_output);
        return Ok(());
    };

    let path = Path::new(save_path);
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent).map_err(|error| {
                format!(
                    "failed to create {} output directory for {}: {}",
                    graph_kind.output_name(),
                    save_path,
                    error
                )
            })?;
        }
    }
    fs::write(path, format!("{}\n", trimmed_output)).map_err(|error| {
        format!(
            "failed to write {} JSON to {}: {}",
            graph_kind.output_name(),
            save_path,
            error
        )
    })?;
    println!("saved {} JSON to {}", graph_kind.output_name(), save_path);
    Ok(())
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
litex -f <input.lit> -isolated -lean <output.lean> : verify every statement in one standalone file, then compile the complete result to Lean
litex -lean-ledger <markdown> <output.lean> : freshly compile every H2 Litex fence into one namespaced Lean file
litex -graph -f <file> <json> : run a file and save a recursive result/proof/FactId graph JSON object
litex -graph -e <code> <json> : run source code and save a recursive result/proof/FactId graph JSON object
litex -graph -r <project> <json> : run a project and save a recursive result/proof/FactId graph JSON object
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
"#;
    result.to_string()
}

#[cfg(test)]
#[path = "../../tests/unit/cli/cli/tests.rs"]
mod tests;
