use super::{
    display_trusted_prefix_report_json, execute_file_in_runtime, execute_repository_target,
    execute_source, record_pipeline_step, render_run_output, render_run_summary,
    resolve_source_file_path, FileExecutionOptions, PipelineTrace, PipelineTraceCapture,
    RepositoryExecutionOptions, RunSummaryRequest,
};
use crate::common::{helper::remove_windows_carriage_return, output_language::OutputLanguage};
use crate::error::RuntimeError;
use crate::module_manager::{discover_repository, RepositoryFileTarget};
use crate::result::StmtResult;
use crate::runtime::{OutputStyle, Runtime, TrustedPrefixReport};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RunTarget {
    Code { source: String, label: String },
    File { path: String },
    Repository { path: String },
}

impl RunTarget {
    pub fn code(source: &str, label: &str) -> Self {
        Self::Code {
            source: source.to_string(),
            label: label.to_string(),
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
    pub trust_before_line: Option<usize>,
    pub trace_pipeline: bool,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            output_style: OutputStyle::Normal,
            strict_mode: false,
            output_language: OutputLanguage::English,
            summarize: false,
            force_isolated: false,
            trust_before_line: None,
            trace_pipeline: false,
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
    pub trusted_prefix_report: Option<TrustedPrefixReport>,
    pub trusted_prefix_setup_rejected: bool,
    pub pipeline_trace: PipelineTrace,
}

impl RunOutcome {
    pub fn prepend_cli_trace(&mut self) {
        self.pipeline_trace.prepend_cli_entry();
    }
}

pub fn run(request: RunRequest) -> RunOutcome {
    let RunRequest { target, options } = request;
    let trace_capture = PipelineTraceCapture::new(options.trace_pipeline);
    record_pipeline_step("pipeline", "pipeline::run", "src/pipeline/run.rs");

    let mut runtime = Runtime::new();
    runtime.set_output_style(options.output_style);
    runtime.strict_mode = options.strict_mode;
    runtime.output_language = options.output_language;

    let mut target_error = None;
    let mut selected_repository_target = None;
    let mut trusted_prefix_report = None;
    let mut trusted_prefix_setup_rejected = false;
    let (target_kind, target_label, stmt_results, runtime_error) = match target {
        RunTarget::Code { source, label } => {
            runtime.start_isolated_source(label.as_str());
            let (results, error) = execute_source(
                remove_windows_carriage_return(source.as_str()).as_str(),
                &mut runtime,
            );
            ("code", label, results, error)
        }
        RunTarget::File { path } => match resolve_source_file_path(path.as_str()) {
            Ok(resolved_path) => {
                let (results, error, report, setup_rejected) = execute_file_in_runtime(
                    resolved_path.as_str(),
                    &mut runtime,
                    FileExecutionOptions {
                        force_isolated: options.force_isolated,
                        trust_before_line: options.trust_before_line,
                    },
                );
                trusted_prefix_report = report;
                trusted_prefix_setup_rejected = setup_rejected;
                ("file", resolved_path, results, error)
            }
            Err(message) => {
                target_error = Some(message);
                ("file", path, Vec::new(), None)
            }
        },
        RunTarget::Repository { path } => {
            let normalized_path = remove_windows_carriage_return(path.as_str());
            match discover_repository(&mut runtime, normalized_path.as_str()) {
                Ok(target) => {
                    selected_repository_target = Some(target);
                    let (results, error) = execute_repository_target(
                        &mut runtime,
                        target,
                        RepositoryExecutionOptions::default(),
                    );
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
    if let Some(report) = trusted_prefix_report.as_ref() {
        let mut trusted_prefix_output = display_trusted_prefix_report_json(report);
        if !output.trim().is_empty() {
            trusted_prefix_output.push('\n');
            trusted_prefix_output.push_str(output.trim());
        }
        output = trusted_prefix_output;
        output.push('\n');
        output.push_str(
            render_run_summary(RunSummaryRequest {
                runtime: &runtime,
                stmt_results: &stmt_results,
                runtime_error: &runtime_error,
                trusted_prefix_report: Some(report),
            })
            .as_str(),
        );
        output.push('\n');
    } else if options.summarize {
        output.push('\n');
        output.push_str(
            render_run_summary(RunSummaryRequest {
                runtime: &runtime,
                stmt_results: &stmt_results,
                runtime_error: &runtime_error,
                trusted_prefix_report: None,
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
        trusted_prefix_report,
        trusted_prefix_setup_rejected,
        pipeline_trace: trace_capture.finish(false),
    }
}
