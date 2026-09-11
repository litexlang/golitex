//! Top-level dispatch for the new pipeline.

use crate::new_pipeline::execute::{ExecStmtResult2, FileRunResult, RunResult};
use crate::new_pipeline::parse::ParsedStatement;
use crate::new_pipeline::runtime::{
    CompletedFile, PipelineError, PipelineResult, RunMode, RunOptions, RunTarget, Runtime,
};
use crate::new_pipeline::tokenize::{TokenBlock, Tokenizer};
use std::fs;
use std::path::{Path, PathBuf};

use super::{cli_arg_e, cli_arg_f, cli_arg_r};

/// Dispatch one parsed command to its command-specific entry point.
pub fn run_litex_code(options: RunOptions) -> PipelineResult<RunResult> {
    if options.mode == RunMode::Unverified {
        return Err(PipelineError::Unsupported(
            "the unverified pipeline is not wired yet".to_string(),
        ));
    }

    match &options.target {
        RunTarget::Eval(_) => cli_arg_e::run_cli_arg_e(options),
        RunTarget::File(_) => cli_arg_f::run_cli_arg_f(options),
        RunTarget::Repository(_) => cli_arg_r::run_cli_arg_r(options),
    }
}

/// A config-expanded module execution plan.
///
/// The loader will later construct this from `litex.config`.  Keeping the
/// plan separate from `Runtime` makes the execution order explicit and keeps
/// filesystem/config parsing out of the scope stack implementation.
pub struct ModuleExecutionPlan {
    pub import_std: Vec<FileSpec>,
    pub import_repos: Vec<ModuleExecutionPlan>,
    pub exports: Vec<FileSpec>,
}

pub struct FileSpec {
    pub name: String,
    pub path: PathBuf,
    pub trusted: bool,
}

impl ModuleExecutionPlan {
    pub fn single_export(path: impl Into<PathBuf>) -> Self {
        let path = path.into();
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .map(str::to_owned)
            .unwrap_or_else(|| path.to_string_lossy().into_owned());
        Self {
            import_std: Vec::new(),
            import_repos: Vec::new(),
            exports: vec![FileSpec {
                name,
                path,
                trusted: false,
            }],
        }
    }
}

/// Execute one module plan in the required order:
/// std imports, imported repositories, then local exports.
pub fn execute_module_plan_verified(
    runtime: &mut Runtime,
    plan: &ModuleExecutionPlan,
    output: &mut Vec<FileRunResult>,
) -> PipelineResult<()> {
    for file in &plan.import_std {
        output.push(execute_one_file_verified(runtime, file)?);
    }
    for imported in &plan.import_repos {
        execute_module_plan_verified(runtime, imported, output)?;
    }
    for file in &plan.exports {
        output.push(execute_one_file_verified(runtime, file)?);
    }
    Ok(())
}

/// The shared `tokenize -> parse -> verified execute` pipeline for one file.
pub fn execute_one_file_verified(
    runtime: &mut Runtime,
    file: &FileSpec,
) -> PipelineResult<FileRunResult> {
    let source = fs::read_to_string(&file.path).map_err(|error| PipelineError::Io {
        path: file.path.clone(),
        message: error.to_string(),
    })?;

    runtime.begin_file(file.path.clone(), file.trusted);
    let statement_results = match runtime.run_code_verified(&source) {
        Ok(results) => results,
        Err(error) => {
            runtime.abort_file();
            return Err(error);
        }
    };

    let completed = runtime.finish_file();
    let result = FileRunResult {
        name: file.name.clone(),
        path: file.path.clone(),
        statement_results,
    };
    runtime.publish_completed_export_file(completed);
    Ok(result)
}

impl Runtime {
    /// Run the middle stages for the currently active file.
    pub fn run_code_verified(&mut self, code: &str) -> PipelineResult<Vec<ExecStmtResult2>> {
        let source_path = self
            .current_file_path()
            .ok_or_else(|| PipelineError::Invariant("no file is active".to_string()))?
            .to_path_buf();
        let token_blocks = Tokenizer::new().tokenize(code, source_path)?;
        let mut results = Vec::new();

        for mut token_block in token_blocks {
            let statement = self.parse_stmt(&mut token_block)?;
            results.push(self.exec_stmt(&statement)?);
        }
        Ok(results)
    }
}

// These imports are kept in this file as a visible checklist of the three
// stage boundaries.  The parser and executor own the actual method bodies.
#[allow(unused_imports)]
fn _stage_types(_token: TokenBlock, _statement: ParsedStatement, _file: CompletedFile) {}

#[allow(dead_code)]
fn _source_path(path: &Path) -> PathBuf {
    path.to_path_buf()
}
