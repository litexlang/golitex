pub(super) mod file_execution;
mod output_rendering;
pub mod repl;
mod repository_execution;
mod run;
pub mod session;
mod source_execution;
mod summary;
mod target;
mod terminal_import;

pub use file_execution::{
    execute_file_in_runtime, execute_isolated_file_in_runtime, resolve_source_file_path,
};
pub use output_rendering::{render_run_output, render_stream_output};

#[allow(deprecated)]
pub use crate::output::{
    display_runtime_error_json, display_stmt_exec_result_json, render_runtime_error_json,
};
pub use crate::runtime::{
    LitexExecution, RuntimeOptions, SummaryOption, VerifyStrictnessPolicy,
};
pub use repl::{run_isolated_repl_with_runtime, run_latex_repl, run_repl};
pub use repository_execution::execute_repository_target;
pub use run::{
    run_eval_command, run_file_command, run_isolated_file_command, run_repository_command,
    RunOutcome,
};
pub use session::{run_session, SessionRequest};
pub use source_execution::SourceRunOutcome;
pub use summary::{render_run_summary, RunSummary, RunSummaryRequest};
pub use target::{ExecutionTarget, RunTarget, RunTargetKind, SessionTarget};
