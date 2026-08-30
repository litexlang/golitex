use super::arguments::{
    parse_global_options, read_non_flag_value_after_flag, read_session_target,
    reject_meaningless_isolated, GlobalOptions,
};
use super::command_handlers::{
    print_or_save_graph_output, run_code_from_e_command_line_flag, run_file_command,
    run_graph_command, run_repository_command, run_runner_command, VERSION,
};
use super::conversion_commands::{
    run_code_extraction_command, run_latex_command, CodeExtractionCommand,
};
use super::lean_commands::{run_lean_file_command, run_lean_ledger_command};
use super::messages::{print_help_message, upgrade_message};
use crate::graph::GraphKind;
use crate::pipeline::{run_repl, run_session, FileRunMode, RunOptions, SessionRequest};
use std::env;
use std::process;

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let GlobalOptions {
        run: run_options,
        isolated,
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
                exit_on_meaningless_isolated(isolated, "-help");
                print_help_message();
                println!();
                println!("If no options are provided, starts interactive REPL mode.");
                return;
            }
            "-version" => {
                exit_on_meaningless_isolated(isolated, "-version");
                println!("Litex Kernel: litex {}", VERSION);
                return;
            }
            "-upgrade" => {
                exit_on_meaningless_isolated(isolated, "-upgrade");
                println!("{}", upgrade_message(VERSION));
                return;
            }
            "-e" => {
                exit_on_meaningless_isolated(isolated, "-e");
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
                    run_lean_file_command(&args, &mut index, &file_path, run_options, isolated);
                    return;
                }
                run_file_command(
                    file_path.as_str(),
                    FileRunMode::from_isolated(isolated),
                    run_options,
                );
                return;
            }
            "-r" => {
                exit_on_meaningless_isolated(isolated, "-r");
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
            "-runner" => {
                index += 1;
                let (ok, output) = match run_runner_command(
                    &args,
                    &mut index,
                    RunOptions {
                        summarize: false,
                        ..run_options
                    },
                    isolated,
                ) {
                    Ok(output) => output,
                    Err(message) => {
                        eprintln!("{}", message);
                        print_help_message();
                        process::exit(2);
                    }
                };
                println!("{}", output.trim());
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
                    RunOptions {
                        summarize: false,
                        ..run_options
                    },
                    isolated,
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
                let target = match read_session_target(&args, &mut index, isolated) {
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
            "-lean-ledger" => {
                exit_on_meaningless_isolated(isolated, "-lean-ledger");
                run_lean_ledger_command(&args, &mut index);
                return;
            }
            "-latex" => {
                run_latex_command(&args, &mut index, run_options.output_language, isolated);
                return;
            }
            "-extractpython" => {
                run_code_extraction_command(
                    &args,
                    &mut index,
                    run_options.output_language,
                    isolated,
                    CodeExtractionCommand::Python,
                );
                return;
            }
            "-extractc" => {
                run_code_extraction_command(
                    &args,
                    &mut index,
                    run_options.output_language,
                    isolated,
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

fn exit_on_meaningless_isolated(isolated: bool, target: &str) {
    if let Err(message) = reject_meaningless_isolated(isolated, target) {
        eprintln!("{}", message);
        print_help_message();
        process::exit(2);
    }
}

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
