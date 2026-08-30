use super::{
    execute_file_in_runtime, execute_repository_target, render_run_output, render_run_summary,
    resolve_source_file_path, FileExecutionOptions, RunSummaryRequest,
};
use crate::error::RuntimeError;
use crate::module_system::{discover_repository, RepositoryFileTarget};
use crate::result::StmtResult;
use crate::runtime::{RunOptions, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RunTargetKind {
    Code,
    File,
    Repository,
    Session,
}

impl RunTargetKind {
    pub fn json_name(self) -> &'static str {
        match self {
            Self::Code => "code",
            Self::File => "file",
            Self::Repository => "repo",
            Self::Session => "session",
        }
    }
}

pub struct RunOutcome {
    pub ok: bool,
    pub target_kind: RunTargetKind,
    pub target_path: Option<String>,
    pub runtime: Runtime,
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
    pub output: String,
    pub target_error: Option<String>,
    pub selected_repository_target: Option<RepositoryFileTarget>,
}

pub fn run_code(source: &str, options: RunOptions) -> RunOutcome {
    let mut runtime = Runtime::new(options);
    runtime.start_isolated_source("<-e>");
    let (stmt_results, runtime_error) = runtime
        .execute_source(remove_windows_carriage_from_str(source).as_str())
        .into_parts();

    finish_run(
        RunTargetKind::Code,
        None,
        runtime,
        stmt_results,
        runtime_error,
        None,
        None,
        options.summarize,
    )
}

pub fn run_file(path: &str, options: RunOptions) -> RunOutcome {
    let mut runtime = Runtime::new(options);
    let mut target_error = None;
    let (target_path, stmt_results, runtime_error) = match resolve_source_file_path(path) {
        Ok(resolved_path) => {
            let (results, error) = execute_file_in_runtime(
                resolved_path.as_str(),
                &mut runtime,
                FileExecutionOptions {
                    force_isolated: options.force_isolated,
                },
            );
            (resolved_path, results, error)
        }
        Err(message) => {
            target_error = Some(message);
            (path.to_string(), Vec::new(), None)
        }
    };

    finish_run(
        RunTargetKind::File,
        Some(target_path),
        runtime,
        stmt_results,
        runtime_error,
        target_error,
        None,
        options.summarize,
    )
}

pub fn run_repository(path: &str, options: RunOptions) -> RunOutcome {
    let mut runtime = Runtime::new(options);
    let normalized_path = remove_windows_carriage_from_str(path);
    let mut selected_repository_target = None;
    let (stmt_results, runtime_error) =
        match discover_repository(&mut runtime, normalized_path.as_str()) {
            Ok(target) => {
                selected_repository_target = Some(target);
                execute_repository_target(&mut runtime, target)
            }
            Err(error) => (Vec::new(), Some(error)),
        };

    finish_run(
        RunTargetKind::Repository,
        Some(normalized_path),
        runtime,
        stmt_results,
        runtime_error,
        None,
        selected_repository_target,
        options.summarize,
    )
}

fn finish_run(
    target_kind: RunTargetKind,
    target_path: Option<String>,
    runtime: Runtime,
    stmt_results: Vec<StmtResult>,
    runtime_error: Option<RuntimeError>,
    target_error: Option<String>,
    selected_repository_target: Option<RepositoryFileTarget>,
    summarize: bool,
) -> RunOutcome {
    let (ok, mut output) = if target_error.is_some() {
        (false, String::new())
    } else {
        render_run_output(&runtime, &stmt_results, &runtime_error)
    };
    if summarize {
        output.push('\n');
        output.push_str(
            render_run_summary(RunSummaryRequest {
                runtime: &runtime,
                stmt_results: &stmt_results,
                runtime_error: &runtime_error,
            })
            .as_str(),
        );
        output.push('\n');
    }

    RunOutcome {
        ok,
        target_kind,
        target_path,
        runtime,
        stmt_results,
        runtime_error,
        output,
        target_error,
        selected_repository_target,
    }
}
