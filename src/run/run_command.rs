use super::output::write_stdout;
use super::run_command_outcome::{HelpResult, RunCommandOutcome, VersionResult};
use super::{run_eval, run_extract, run_repl};
use crate::launch_command::LaunchCommand;
use crate::run_module::{run_file_with_config, run_project};
use crate::runtime::RuntimeResult;
use crate::LITEX;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub fn run_command(command: LaunchCommand) -> RuntimeResult<RunCommandOutcome> {
    match command {
        LaunchCommand::Help { .. } => {
            let entries = print_help_message()?;
            Ok(RunCommandOutcome::Help(HelpResult::new(entries)))
        }
        LaunchCommand::Version { .. } => {
            write_stdout(format_args!("{} {}\n", LITEX, VERSION))?;
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
            let result = run_file_with_config(command)?;
            Ok(RunCommandOutcome::RunFile(result))
        }
        command @ LaunchCommand::Repository { .. } => {
            let result = run_project(command)?;
            Ok(RunCommandOutcome::RunRepo(result))
        }
        command @ LaunchCommand::Extract { .. } => {
            let result = run_extract::run_extract(command)?;
            Ok(RunCommandOutcome::Extract(result))
        }
    }
}

fn print_help_message() -> RuntimeResult<Vec<String>> {
    let bin = LITEX.to_ascii_lowercase();
    let usage = vec![
        format!("{}", bin),
        format!("{} -e <code>", bin),
        format!("{} -f <file>", bin),
        format!("{} -r <repository>", bin),
        format!("{} -extractpython <code>", bin),
        format!("{} -extractpython -f <file>", bin),
        format!("{} -extractpython -r <repository>", bin),
        format!("{} -extractc <code>", bin),
        format!("{} -extractc -f <file>", bin),
        format!("{} -extractc -r <repository>", bin),
        format!("{} -lang zh -e <code>", bin),
        format!("{} -strict -e <code>", bin),
        format!("{} -f <file> -session", bin),
        format!("{} -help", bin),
        format!("{} -version", bin),
    ];
    let notes = vec![
        "-session keeps the Runtime env open and continues as REPL after -e/-f/-r.".to_string(),
        "-strict forbids `trust` / `trust have` / user `axiom`; abstract predicate declarations and named foundation releases are allowed.".to_string(),
        "-lang en|zh|zh-hant|fr|ru|es|ar|ja|ko|vi selects JSON output language (default en; English language names also accepted).".to_string(),
        "-extractpython / -extractc emit verified numeric/algo fragments as Python or C.".to_string(),
    ];
    write_stdout(format_args!("{}\n\nUsage:\n", LITEX))?;
    for entry in &usage {
        write_stdout(format_args!("  {}\n", entry))?;
    }
    write_stdout(format_args!("\n"))?;
    for note in &notes {
        write_stdout(format_args!("{}\n", note))?;
    }
    let mut entries = vec![LITEX.to_string()];
    entries.extend(usage);
    entries.extend(notes);
    Ok(entries)
}
