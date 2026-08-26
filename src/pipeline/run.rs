use super::{
    execute_file_in_runtime, execute_repository_target, render_run_output, render_run_summary,
    resolve_source_file_path, FileExecutionOptions, RunSummaryRequest, SourceImportPolicy,
};
use crate::common::{helper::remove_windows_carriage_from_str, output_language::OutputLanguage};
use crate::error::RuntimeError;
use crate::module_manager::{discover_repository, RepositoryFileTarget};
use crate::result::StmtResult;
use crate::runtime::{OutputStyle, Runtime};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunTarget {
    Code {
        source: String,
        source_label: String,
    },
    File {
        path: String,
    },
    Repository {
        path: String,
    },
}

impl RunTarget {
    /// Create an inline source target. `source_label` is the synthetic file name
    /// used in diagnostics because inline code has no filesystem path.
    pub fn code(source: &str, source_label: &str) -> Self {
        Self::Code {
            source: source.to_string(),
            source_label: source_label.to_string(),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunOptions {
    pub output_style: OutputStyle,
    pub strict_mode: bool,
    pub output_language: OutputLanguage,
    pub summarize: bool,
    pub force_isolated: bool,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            output_style: OutputStyle::Normal,
            strict_mode: false,
            output_language: OutputLanguage::English,
            summarize: false,
            force_isolated: false,
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
    pub target_kind: String,
    pub target_label: String,
    pub runtime: Runtime,
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
    pub output: String,
    pub target_error: Option<String>,
    pub selected_repository_target: Option<RepositoryFileTarget>,
}

pub fn run(request: RunRequest) -> RunOutcome {
    let RunRequest { target, options } = request;

    let mut runtime = Runtime::new(
        options.output_style,
        options.strict_mode,
        options.output_language,
    );

    let mut target_error = None;
    let mut selected_repository_target = None;
    let (target_kind, target_label, stmt_results, runtime_error) = match target {
        RunTarget::Code {
            source,
            source_label,
        } => {
            runtime.start_isolated_source(source_label.as_str());
            let (results, error) = runtime
                .execute_source(
                    remove_windows_carriage_from_str(source.as_str()).as_str(),
                    SourceImportPolicy::UseRuntimePolicy,
                )
                .into_parts();
            ("code", source_label, results, error)
        }
        RunTarget::File { path } => match resolve_source_file_path(path.as_str()) {
            Ok(resolved_path) => {
                let (results, error) = execute_file_in_runtime(
                    resolved_path.as_str(),
                    &mut runtime,
                    FileExecutionOptions {
                        force_isolated: options.force_isolated,
                    },
                );
                ("file", resolved_path, results, error)
            }
            Err(message) => {
                target_error = Some(message);
                ("file", path, Vec::new(), None)
            }
        },
        RunTarget::Repository { path } => {
            let normalized_path = remove_windows_carriage_from_str(path.as_str());
            match discover_repository(&mut runtime, normalized_path.as_str()) {
                Ok(target) => {
                    selected_repository_target = Some(target);
                    let (results, error) = execute_repository_target(&mut runtime, target);
                    ("repo", normalized_path, results, error)
                }
                Err(error) => ("repo", normalized_path, Vec::new(), Some(error)),
            }
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
        target_kind: target_kind.to_string(),
        target_label,
        runtime,
        stmt_results,
        runtime_error,
        output,
        target_error,
        selected_repository_target,
    }
}
