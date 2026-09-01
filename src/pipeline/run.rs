use super::file_execution::file_execution_option;
use super::{
    execute_file_in_runtime, execute_isolated_file_in_runtime, execute_repository_target,
    render_run_output, render_run_summary, resolve_source_file_path, ExecutionTarget,
    RunSummaryRequest, RunTarget,
};
use crate::error::RuntimeError;
use crate::module_system::discover_repository;
use crate::result::StmtResult;
use crate::runtime::{ExecutionOption, RunOptions, Runtime};
use crate::syntax::source_formatting::remove_windows_carriage_from_str;

pub struct RunOutcome {
    pub ok: bool,
    pub target: RunTarget,
    pub runtime: Runtime,
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
    pub output: String,
    pub target_error: Option<String>,
}

pub fn run_code(source: &str, options: RunOptions) -> RunOutcome {
    let options = options.with_execution(ExecutionOption::Eval);
    let mut runtime = Runtime::new(options);
    let target = RunTarget::Eval;
    runtime.start_isolated_source(ExecutionTarget::Run(target.clone()).source_label());
    let (stmt_results, runtime_error) = runtime
        .execute_source(remove_windows_carriage_from_str(source).as_str())
        .into_parts();

    finish_run(
        target,
        runtime,
        stmt_results,
        runtime_error,
        None,
        options.should_summarize(),
    )
}

pub fn run_file(path: &str, options: RunOptions) -> RunOutcome {
    let resolved_path = resolve_source_file_path(path);
    let execution = resolved_path
        .as_ref()
        .map(|path| file_execution_option(path.as_str()))
        .unwrap_or(ExecutionOption::File);
    let options = options.with_execution(execution);
    let mut runtime = Runtime::new(options);
    let mut target_error = None;
    let (target_path, stmt_results, runtime_error) = match resolved_path {
        Ok(resolved_path) => {
            let (results, error) = match execution {
                ExecutionOption::File => {
                    execute_file_in_runtime(resolved_path.as_str(), &mut runtime)
                }
                ExecutionOption::IsolatedFile => {
                    execute_isolated_file_in_runtime(resolved_path.as_str(), &mut runtime)
                }
                _ => unreachable!("file context resolved to a non-file execution option"),
            };
            (resolved_path, results, error)
        }
        Err(message) => {
            target_error = Some(message);
            (path.to_string(), Vec::new(), None)
        }
    };

    let target = match execution {
        ExecutionOption::File => RunTarget::File { path: target_path },
        ExecutionOption::IsolatedFile => RunTarget::IsolatedFile { path: target_path },
        _ => unreachable!("file context resolved to a non-file execution option"),
    };
    finish_run(
        target,
        runtime,
        stmt_results,
        runtime_error,
        target_error,
        options.should_summarize(),
    )
}

pub fn run_isolated_file(path: &str, options: RunOptions) -> RunOutcome {
    let options = options.with_execution(ExecutionOption::IsolatedFile);
    let mut runtime = Runtime::new(options);
    let mut target_error = None;
    let (target_path, stmt_results, runtime_error) = match resolve_source_file_path(path) {
        Ok(resolved_path) => {
            let (results, error) =
                execute_isolated_file_in_runtime(resolved_path.as_str(), &mut runtime);
            (resolved_path, results, error)
        }
        Err(message) => {
            target_error = Some(message);
            (path.to_string(), Vec::new(), None)
        }
    };

    finish_run(
        RunTarget::IsolatedFile { path: target_path },
        runtime,
        stmt_results,
        runtime_error,
        target_error,
        options.should_summarize(),
    )
}

pub fn run_repository(path: &str, options: RunOptions) -> RunOutcome {
    let options = options.with_execution(ExecutionOption::Repo);
    let mut runtime = Runtime::new(options);
    let normalized_path = remove_windows_carriage_from_str(path);
    let (stmt_results, runtime_error) =
        match discover_repository(&mut runtime, normalized_path.as_str()) {
            Ok(target) => execute_repository_target(&mut runtime, target),
            Err(error) => (Vec::new(), Some(error)),
        };

    finish_run(
        RunTarget::Repository {
            path: normalized_path,
        },
        runtime,
        stmt_results,
        runtime_error,
        None,
        options.should_summarize(),
    )
}

fn finish_run(
    target: RunTarget,
    runtime: Runtime,
    stmt_results: Vec<StmtResult>,
    runtime_error: Option<RuntimeError>,
    target_error: Option<String>,
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
        target,
        runtime,
        stmt_results,
        runtime_error,
        output,
        target_error,
    }
}
