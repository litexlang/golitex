use super::command::CliCommand;
use super::run_command_outcome::{HelpResult, RunCommandOutcome, VersionResult};
use super::{run_eval, run_file, run_repo};
use crate::new_pipeline::runtime::RuntimeResult;

pub const NEW_PIPELINE_VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_command(command: CliCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        CliCommand::Help => {
            let entries = print_help_message();
            Ok(RunCommandOutcome::Help(HelpResult::new(entries)))
        }
        CliCommand::Version => {
            println!("litex new_pipeline {}", NEW_PIPELINE_VERSION);
            Ok(RunCommandOutcome::Version(VersionResult::new(
                NEW_PIPELINE_VERSION,
            )))
        }
        CliCommand::Eval(code) => {
            let result = run_eval::run_eval(code)?;
            Ok(RunCommandOutcome::RunEval(result))
        }
        CliCommand::File(path) => {
            let result = run_file::run_file(path)?;
            Ok(RunCommandOutcome::RunFile(result))
        }
        CliCommand::Repository(path) => {
            let result = run_repo::run_repo(path)?;
            Ok(RunCommandOutcome::RunRepo(result))
        }
    }
}

fn print_help_message() -> Vec<String> {
    let entries = vec![
        "litex new_pipeline (test track)".to_string(),
        "LITEX_NEW_PIPELINE=1 litex -e <code>".to_string(),
        "LITEX_NEW_PIPELINE=1 litex -f <file>".to_string(),
        "LITEX_NEW_PIPELINE=1 litex -r <repository>".to_string(),
        "LITEX_NEW_PIPELINE=1 litex -help".to_string(),
        "LITEX_NEW_PIPELINE=1 litex -version".to_string(),
        "Without LITEX_NEW_PIPELINE, the legacy CLI is used.".to_string(),
    ];
    println!("{}", entries[0]);
    println!();
    println!("Usage:");
    for entry in &entries[1..6] {
        println!("  {}", entry);
    }
    println!();
    println!("{}", entries[6]);
    entries
}
