use super::arguments::{
    parse_global_options, read_non_flag_value_after_flag, read_session_preload,
    validate_session_preload,
};
use super::command_handlers::{
    print_or_save_graph_output, run_code_command, run_file_command, run_graph_command,
    run_repository_command, run_runner_command, VERSION,
};
use super::conversion_commands::{run_latex_command, run_python_command};
use super::lean_commands::{run_lean_file_command, run_lean_ledger_command};
use super::messages::{print_help_message, upgrade_message};
use crate::graph::GraphKind;
use crate::pipeline::{run_repl, run_session, ReplOptions, RunOptions, SessionRequest};
use std::env;
use std::process;

pub fn run_cli() {
    let mut args: Vec<String> = env::args().skip(1).collect();
    let cli_options = match parse_global_options(&mut args) {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };
    let run_options = cli_options.run_options();
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
                run_code_command(code.as_str(), run_options);
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
            "-runner" => {
                index += 1;
                let (ok, output) = match run_runner_command(
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
                if let Err(message) = validate_session_preload(cli_options.force_isolated, &preload)
                {
                    eprintln!("{}", message);
                    print_help_message();
                    process::exit(2);
                }
                run_session(SessionRequest::new(
                    RunOptions {
                        summarize: false,
                        ..run_options
                    },
                    preload,
                ));
                return;
            }
            "-lean-ledger" => {
                run_lean_ledger_command(&args, &mut index);
                return;
            }
            "-latex" => {
                run_latex_command(
                    &args,
                    &mut index,
                    cli_options.output_language,
                    cli_options.force_isolated,
                );
                return;
            }
            "-python" => {
                run_python_command(
                    &args,
                    &mut index,
                    cli_options.output_language,
                    cli_options.force_isolated,
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

    run_repl(
        VERSION,
        ReplOptions::new(
            cli_options.output_style,
            cli_options.strict_mode,
            cli_options.output_language,
        ),
    );
}

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
