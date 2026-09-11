use super::command::CliCommand;
use super::{run_eval, run_file, run_repo};
use crate::new_pipeline::runtime::RuntimeResult;

pub const NEW_PIPELINE_VERSION: &str = env!("CARGO_PKG_VERSION");

#[derive(Debug)]
pub enum RunCommandOutcome {
    Ran,
    Help,
    Version,
}

pub fn run_command(command: CliCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        CliCommand::Help => {
            print_help_message();
            Ok(RunCommandOutcome::Help)
        }
        CliCommand::Version => {
            println!("litex new_pipeline {}", NEW_PIPELINE_VERSION);
            Ok(RunCommandOutcome::Version)
        }
        CliCommand::Eval(code) => {
            run_eval::run_eval(code)?;
            Ok(RunCommandOutcome::Ran)
        }
        CliCommand::File(path) => {
            run_file::run_file(path)?;
            Ok(RunCommandOutcome::Ran)
        }
        CliCommand::Repository(path) => {
            run_repo::run_repo(path)?;
            Ok(RunCommandOutcome::Ran)
        }
    }
}

fn print_help_message() {
    println!("litex new_pipeline (test track)");
    println!();
    println!("Usage:");
    println!("  LITEX_NEW_PIPELINE=1 litex -e <code>");
    println!("  LITEX_NEW_PIPELINE=1 litex -f <file>");
    println!("  LITEX_NEW_PIPELINE=1 litex -r <repository>");
    println!("  LITEX_NEW_PIPELINE=1 litex -help");
    println!("  LITEX_NEW_PIPELINE=1 litex -version");
    println!();
    println!("Without LITEX_NEW_PIPELINE, the legacy CLI is used.");
}
