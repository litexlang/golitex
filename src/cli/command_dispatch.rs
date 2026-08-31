use super::arguments::{
    parse_global_options, read_non_flag_value_after_flag, read_session_target,
    validate_cli_combination,
};
use super::command_handlers::{
    print_or_save_graph_output, run_code_from_e_command_line_flag, run_file_command,
    run_graph_command, run_repository_command, VERSION,
};
use super::conversion_commands::{
    run_code_extraction_command, run_latex_command, CodeExtractionCommand,
};
use super::lean_commands::run_lean_file_command;
use super::messages::print_help_message;
use crate::graph::GraphKind;
use crate::pipeline::{run_repl, run_session, RunOptions, SessionRequest};
use std::env;
use std::process;

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let run_options = match parse_global_options(&mut args) {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    if let Err(message) = validate_cli_combination(&args, run_options.is_isolated) {
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
                run_code_from_e_command_line_flag(code.as_str(), run_options);
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
                    run_lean_file_command(&args, &mut index, &file_path, run_options);
                    return;
                }
                run_file_command(file_path.as_str(), run_options);
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
                run_repository_command(repo_path.as_str(), run_options);
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
                    RunOptions {
                        summarize: false,
                        ..run_options
                    },
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
                let target = match read_session_target(&args, &mut index, run_options.is_isolated) {
                    Ok(value) => value,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                run_session(SessionRequest::new(
                    RunOptions {
                        summarize: false,
                        ..run_options
                    },
                    target,
                ));
                return;
            }
            "-latex" => {
                run_latex_command(&args, &mut index, run_options);
                return;
            }
            "-extractpython" => {
                run_code_extraction_command(
                    &args,
                    &mut index,
                    run_options,
                    CodeExtractionCommand::Python,
                );
                return;
            }
            "-extractc" => {
                run_code_extraction_command(
                    &args,
                    &mut index,
                    run_options,
                    CodeExtractionCommand::C,
                );
                return;
            }
            other => {
                eprintln!("unknown argument: {}", other);
                print_help_message();
                process::exit(2);
            }
        }
    }

    run_repl(VERSION, run_options);
}

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
