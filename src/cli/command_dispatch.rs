use super::command::{parse_cli_command, CliCommand};
use super::command_handlers::{
    print_or_save_graph_output, run_code_command, run_file_command, run_graph_command,
    run_repository_command, VERSION,
};
use super::conversion_commands::{run_code_extraction_command, run_latex_command};
use super::lean_commands::run_lean_file_command;
use super::messages::print_help_message;
use crate::prelude::*;
use std::env;
use std::process;

pub fn run_cli() {
    let raw_args: Vec<String> = env::args().skip(1).collect();
    let command = match parse_cli_command(&raw_args) {
        Ok(command) => command,
        Err(message) => {
            eprintln!("{}", message);
            print_help_message();
            process::exit(2);
        }
    };

    match command {
        CliCommand::Repl(options) => run_repl(VERSION, options),
        CliCommand::Help => {
            print_help_message();
            println!();
            println!("If no options are provided, starts interactive REPL mode.");
        }
        CliCommand::Version => println!("Litex Kernel: litex {}", VERSION),
        CliCommand::Execute { target, options } => match options.execution() {
            ExecutionOption::Eval => run_code_command(target.as_str(), options),
            ExecutionOption::File | ExecutionOption::IsolatedFile => {
                run_file_command(target.as_str(), options)
            }
            ExecutionOption::Repo => run_repository_command(target.as_str(), options),
            ExecutionOption::Repl | ExecutionOption::Session | ExecutionOption::IsolatedSession => {
                unreachable!("execute command was resolved to a non-batch target")
            }
        },
        CliCommand::Graph {
            kind,
            target,
            save_path,
            options,
        } => {
            let (ok, output) = run_graph_command(kind, target.as_str(), options);
            if let Err(message) = print_or_save_graph_output(kind, &output, save_path.as_deref()) {
                eprintln!("{}", message);
                process::exit(1);
            }
            if !ok {
                process::exit(1);
            }
        }
        CliCommand::Session { file_path, options } => {
            let target = match (options.execution(), file_path) {
                (ExecutionOption::Session, None) => SessionTarget::CurrentDirectory,
                (ExecutionOption::IsolatedSession, None) => SessionTarget::Isolated,
                (ExecutionOption::Session, Some(path)) => SessionTarget::File {
                    path,
                    mode: FileRunMode::Project,
                },
                (ExecutionOption::IsolatedSession, Some(path)) => SessionTarget::File {
                    path,
                    mode: FileRunMode::Isolated,
                },
                _ => unreachable!("session command was resolved to a non-session target"),
            };
            run_session(SessionRequest::new(options, target));
        }
        CliCommand::LatexRepl => run_latex_repl(VERSION),
        CliCommand::Latex { target, options } => run_latex_command(target.as_str(), options),
        CliCommand::Extract {
            kind,
            target,
            options,
        } => run_code_extraction_command(target.as_str(), options, kind),
        CliCommand::Lean {
            input_path,
            output_path,
        } => run_lean_file_command(input_path.as_str(), output_path.as_str()),
    }
}

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
