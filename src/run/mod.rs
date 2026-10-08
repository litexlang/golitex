pub mod output;
pub mod run_command;
pub mod run_command_outcome;
pub mod run_compile_to_latex;
pub mod run_compile_to_lean;
pub mod run_eval;
pub mod run_extract_executable_code;
pub mod run_litex_code;
pub mod run_repl;

#[cfg(test)]
#[path = "../../tests/unit/run/binding_lifecycle/tests.rs"]
mod binding_lifecycle_tests;

#[cfg(test)]
#[path = "../../tests/unit/run/latex_command/tests.rs"]
mod latex_command_tests;

pub use crate::launch_command::{
    parse_launch_command, CodeExtractionTarget, ExtractInput, LatexInput, LaunchCommand,
    OutputLanguage,
};
pub use run_command::{run_command, VERSION};
pub use run_command_outcome::{
    CompileToLatexResult, ExtractExecutableCodeResult, HelpResult, RunCommandOutcome,
    RunEvalResult, RunFileResult, RunLitexCodeResult, RunRepoResult, RunSessionError,
    VersionResult,
};
