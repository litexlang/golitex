use super::command::{parse_cli_command, CliCommand};
use super::command_handlers::{run_command, run_graph_command, VERSION};
use super::conversion_commands::{run_code_extraction_command, run_latex_command};
use super::json_output::{render_cli_error, render_version};
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
            println!("{}", render_cli_error(message.as_str()));
            process::exit(2);
        }
    };

    match command {
        CliCommand::Repl(options) => run_repl(VERSION, options),
        CliCommand::Help => print_help_message(),
        CliCommand::Version => println!("{}", render_version(VERSION)),
        CliCommand::Execute { target, options } => {
            if !run_command(target.as_str(), options) {
                process::exit(1);
            }
        }
        CliCommand::Graph {
            kind,
            target,
            save_path,
            options,
        } => {
            if !run_graph_command(kind, target.as_str(), save_path.as_deref(), options) {
                process::exit(1);
            }
        }
        CliCommand::Session { file_path, options } => {
            let target = match (options.execution(), file_path) {
                (ExecutionOption::Session, None) => SessionTarget::CurrentDirectory,
                (ExecutionOption::IsolatedSession, None) => SessionTarget::Isolated,
                (ExecutionOption::Session, Some(path)) => SessionTarget::File { path },
                (ExecutionOption::IsolatedSession, Some(path)) => {
                    SessionTarget::IsolatedFile { path }
                }
                _ => unreachable!("session command was resolved to a non-session target"),
            };
            run_session(SessionRequest::new(options, target));
        }
        CliCommand::LatexRepl => run_latex_repl(VERSION),
        CliCommand::Latex { target, options } => {
            if !run_latex_command(target.as_str(), options) {
                process::exit(1);
            }
        }
        CliCommand::Extract {
            kind,
            target,
            options,
        } => {
            if !run_code_extraction_command(target.as_str(), options, kind) {
                process::exit(1);
            }
        }
        CliCommand::Lean {
            input_path,
            output_path,
        } => {
            if !run_lean_file_command(input_path.as_str(), output_path.as_str()) {
                process::exit(1);
            }
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/cli/command_dispatch/tests.rs"]
mod tests;
