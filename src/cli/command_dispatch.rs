use super::arguments::{
    parse_global_options, read_any_value_after_flag, read_non_flag_value_after_flag,
    read_session_preload, validate_session_preload, CliOptions,
};
use super::command_handlers::{
    print_or_save_graph_output, run_code_command, run_file_command, run_graph_command,
    run_repository_command, run_runner_command, string_with_trimmed_outer_newlines, GraphKind,
    VERSION,
};
use super::conversion_commands::{
    compile_code_to_latex, compile_code_to_python, compile_file_to_latex, compile_file_to_python,
    compile_repo_to_latex, compile_repo_to_python,
};
use super::messages::{print_help_message, upgrade_message};
use crate::prelude::*;
use crate::stmt_result_to_lean_compiler::{
    compile_litex_file_to_lean_file, compile_litex_markdown_code_blocks_to_lean_file,
};
use std::env;
use std::path::Path;
use std::process;

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
                run_code_command(
                    code.as_str(),
                    output_style,
                    strict_mode,
                    output_language,
                    summarize_output,
                );
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

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
