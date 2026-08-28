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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunTarget {
    Code { source: String },
    File { path: String },
    Repository { path: String },
}

impl RunTarget {
    pub fn code(source: &str) -> Self {
        Self::Code {
            source: source.to_string(),
        }
    }

    pub fn file(path: &str) -> Self {
        Self::File {
            path: path.to_string(),
        }
    }

    pub fn repository(path: &str) -> Self {
        Self::Repository {
            path: path.to_string(),
        }
    }
}

pub struct RunRequest {
    pub target: RunTarget,
    pub options: RunOptions,
}

impl RunRequest {
    pub fn new(target: RunTarget, options: RunOptions) -> Self {
        Self { target, options }
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

pub fn run(request: RunRequest) -> RunOutcome {
    let RunRequest { target, options } = request;

    let mut runtime = Runtime::new(options);

    let mut target_error = None;
    let mut selected_repository_target = None;
    let (target_kind, target_path, stmt_results, runtime_error) = match target {
        RunTarget::Code { source } => {
            let (stmt_results, runtime_error) = runtime.run_code_target(source);
            (RunTargetKind::Code, None, stmt_results, runtime_error)
        }
        RunTarget::File { path } => {
            let (target_path, stmt_results, runtime_error) =
                runtime.run_file_target(path, options.force_isolated, &mut target_error);
            (
                RunTargetKind::File,
                Some(target_path),
                stmt_results,
                runtime_error,
            )
        }
        RunTarget::Repository { path } => {
            let (target_path, stmt_results, runtime_error) =
                runtime.run_repository_target(path, &mut selected_repository_target);
            (
                RunTargetKind::Repository,
                Some(target_path),
                stmt_results,
                runtime_error,
            )
        }
    };

    let (ok, mut output) = if target_error.is_some() {
        (false, String::new())
    } else {
        render_run_output(&runtime, &stmt_results, &runtime_error)
    };
    if options.summarize {
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

impl Runtime {
    fn run_code_target(&mut self, source: String) -> (Vec<StmtResult>, Option<RuntimeError>) {
        self.start_isolated_source("entry");
        let (results, error) = self
            .execute_source(remove_windows_carriage_from_str(source.as_str()).as_str())
            .into_parts();
        (results, error)
    }

    fn run_file_target(
        &mut self,
        path: String,
        force_isolated: bool,
        target_error: &mut Option<String>,
    ) -> (String, Vec<StmtResult>, Option<RuntimeError>) {
        match resolve_source_file_path(path.as_str()) {
            Ok(resolved_path) => {
                let (results, error) = execute_file_in_runtime(
                    resolved_path.as_str(),
                    self,
                    FileExecutionOptions { force_isolated },
                );
                (resolved_path, results, error)
            }
            Err(message) => {
                *target_error = Some(message);
                (path, Vec::new(), None)
            }
        }
    }

    fn run_repository_target(
        &mut self,
        path: String,
        selected_repository_target: &mut Option<RepositoryFileTarget>,
    ) -> (String, Vec<StmtResult>, Option<RuntimeError>) {
        let normalized_path = remove_windows_carriage_from_str(path.as_str());
        match discover_repository(self, normalized_path.as_str()) {
            Ok(target) => {
                *selected_repository_target = Some(target);
                let (results, error) = execute_repository_target(self, target);
                (normalized_path, results, error)
            }
            Err(error) => (normalized_path, Vec::new(), Some(error)),
        }
    }
}
