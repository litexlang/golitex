use super::run_command_outcome::{HelpResult, RunCommandOutcome, VersionResult};
use super::{run_eval, run_extract, run_file, run_repl, run_repo};
use crate::launch_command::LaunchCommand;
use crate::runtime::RuntimeResult;
use crate::LITEX;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_command(command: LaunchCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        LaunchCommand::Help { .. } => {
            let entries = print_help_message();
            Ok(RunCommandOutcome::Help(HelpResult::new(entries)))
        }
        LaunchCommand::Version { .. } => {
            println!("{} {}", LITEX, VERSION);
            Ok(RunCommandOutcome::Version(VersionResult::new(VERSION)))
        }
        command @ LaunchCommand::Repl { .. } => {
            run_repl::run_repl(command)?;
            Ok(RunCommandOutcome::RunRepl)
        }
        command @ LaunchCommand::Eval { .. } => {
            let result = run_eval::run_eval(command)?;
            Ok(RunCommandOutcome::RunEval(result))
        }
        command @ LaunchCommand::File { .. } => {
            let result = run_file::run_file(command)?;
            Ok(RunCommandOutcome::RunFile(result))
        }
        command @ LaunchCommand::Repository { .. } => {
            let result = run_repo::run_repo(command)?;
            Ok(RunCommandOutcome::RunRepo(result))
        }
        command @ LaunchCommand::Extract { .. } => {
            let result = run_extract::run_extract(command)?;
            Ok(RunCommandOutcome::Extract(result))
        }
    }
}

fn print_help_message() -> Vec<String> {
    let bin = LITEX.to_ascii_lowercase();
    let entries = vec![
        format!("{}", LITEX),
        format!("{}", bin),
        format!("{} -e <code>", bin),
        format!("{} -f <file>", bin),
        format!("{} -r <repository>", bin),
        format!("{} -extractpython <code>", bin),
        format!("{} -extractpython -f <file>", bin),
        format!("{} -extractc <code>", bin),
        format!("{} -extractc -f <file>", bin),
        format!("{} -lang zh -e <code>", bin),
        format!("{} -strict -e <code>", bin),
        format!("{} -f <file> -session", bin),
        format!("{} -help", bin),
        format!("{} -version", bin),
        "-session keeps the Runtime env open and continues as REPL after -e/-f/-r.".to_string(),
        "-strict forbids `trust` / `trust have` / `abstract_prop`.".to_string(),
        "-lang en|english|zh|chinese selects JSON / status output language (default en).".to_string(),
        "-extractpython / -extractc emit verified numeric/algo fragments as Python or C.".to_string(),
    ];
    println!("{}", entries[0]);
    println!();
    println!("Usage:");
    for entry in &entries[1..14] {
        println!("  {}", entry);
    }
    println!();
    println!("{}", entries[14]);
    println!("{}", entries[15]);
    println!("{}", entries[16]);
    println!("{}", entries[17]);
    entries
}
