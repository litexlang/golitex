use super::{
    execute_top_level_statement, execute_top_level_statement_in_trusted_prefix_run,
    record_pipeline_step,
};
use crate::common::keywords::TRY;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct, UnknownRuntimeError};
use crate::parse::{TokenBlock, Tokenizer};
use crate::result::StmtResult;
use crate::runtime::{ExecutionMode, Runtime};
use crate::stmt::{CommandStmt, ProofBlockStmt, Stmt};
use std::time::Instant;

pub fn execute_source(
    source_code: &str,
    runtime: &mut Runtime,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let outcome = execute_source_with_options(source_code, runtime, SourceRunOptions::default());
    (outcome.stmt_results, outcome.runtime_error)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceRunFailureKind {
    TryStmt,
    Other,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub enum SourceImportPolicy {
    #[default]
    UseRuntimePolicy,
    Reject(String),
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SourceRunOptions {
    pub trust_before_line: Option<usize>,
    pub import_policy: SourceImportPolicy,
}

pub struct SourceRunOutcome {
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
    pub failure_kind: Option<SourceRunFailureKind>,
}

impl SourceRunOutcome {
    fn success(stmt_results: Vec<StmtResult>) -> Self {
        Self {
            stmt_results,
            runtime_error: None,
            failure_kind: None,
        }
    }

    fn failure(
        stmt_results: Vec<StmtResult>,
        runtime_error: RuntimeError,
        failure_kind: SourceRunFailureKind,
    ) -> Self {
        Self {
            stmt_results,
            runtime_error: Some(runtime_error),
            failure_kind: Some(failure_kind),
        }
    }
}

pub fn execute_source_with_options(
    source_code: &str,
    runtime: &mut Runtime,
    options: SourceRunOptions,
) -> SourceRunOutcome {
    record_pipeline_step(
        "source pipeline",
        "pipeline::execute_source",
        "src/pipeline/source_execution.rs",
    );
    if let Err(error) = require_active_source_context(runtime) {
        return SourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
    }

    let blocks = match tokenize_source_code(source_code, runtime) {
        Ok(blocks) => blocks,
        Err((error, failure_kind)) => {
            return SourceRunOutcome::failure(vec![], error, failure_kind);
        }
    };
    if let Some(before_line) = options.trust_before_line {
        if let Err(error) = validate_trusted_prefix_boundary(&blocks, runtime, before_line) {
            return SourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
        }
    }

    execute_source_blocks(blocks, runtime, &options)
}

fn require_active_source_context(runtime: &Runtime) -> Result<(), RuntimeError> {
    if runtime.has_active_execution_frame() {
        return Ok(());
    }

    Err(ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
        "runtime has no active source context; initialize a file or repository before running source"
            .to_string(),
    ))
    .into())
}

fn tokenize_source_code(
    source_code: &str,
    runtime: &Runtime,
) -> Result<Vec<TokenBlock>, (RuntimeError, SourceRunFailureKind)> {
    let failure_kind = if source_code
        .lines()
        .find(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .is_some_and(|line| line.trim_end() == "try:")
    {
        SourceRunFailureKind::TryStmt
    } else {
        SourceRunFailureKind::Other
    };
    Tokenizer::new()
        .parse_blocks(source_code, runtime.current_file_path_rc())
        .map_err(|error| (error, failure_kind))
}

fn validate_trusted_prefix_boundary(
    blocks: &[TokenBlock],
    runtime: &Runtime,
    before_line: usize,
) -> Result<(), RuntimeError> {
    let statement_lines = blocks
        .iter()
        .map(|block| block.line_file.0)
        .collect::<Vec<_>>();
    if statement_lines.contains(&before_line) {
        return Ok(());
    }

    let message = trusted_prefix_boundary_error_message(
        runtime.current_file_path_rc().as_ref(),
        before_line,
        &statement_lines,
    );
    Err(
        ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
            message,
            (before_line, runtime.current_file_path_rc()),
        ))
        .into(),
    )
}

fn execute_source_blocks(
    blocks: Vec<TokenBlock>,
    runtime: &mut Runtime,
    options: &SourceRunOptions,
) -> SourceRunOutcome {
    let profile_repository_run = std::env::var_os("LITEX_PROFILE_REPOSITORY").is_some();
    let mut stmt_results: Vec<StmtResult> = Vec::new();
    for mut block in blocks {
        let statement_start = profile_repository_run.then(Instant::now);
        let parse_failure_kind = if block.current_token_is_equal_to(TRY) {
            SourceRunFailureKind::TryStmt
        } else {
            SourceRunFailureKind::Other
        };
        let stmt = match runtime.parse_statement(&mut block) {
            Ok(stmt) => stmt,
            Err(error) => {
                return SourceRunOutcome::failure(stmt_results, error, parse_failure_kind);
            }
        };
        if let (SourceImportPolicy::Reject(message), Stmt::Command(CommandStmt::ImportStmt(_))) =
            (&options.import_policy, &stmt)
        {
            return SourceRunOutcome::failure(
                stmt_results,
                UnknownRuntimeError(RuntimeErrorStruct::new(
                    None,
                    message.clone(),
                    stmt.line_file(),
                    None,
                    vec![],
                ))
                .into(),
                SourceRunFailureKind::Other,
            );
        }
        let execution_failure_kind =
            if matches!(&stmt, Stmt::ProofBlock(ProofBlockStmt::TryStmt(_))) {
                SourceRunFailureKind::TryStmt
            } else {
                SourceRunFailureKind::Other
            };
        let trusted_prefix_statement = options
            .trust_before_line
            .is_some_and(|before_line| stmt.line_file().0 < before_line);
        let previous_execution_mode = trusted_prefix_statement
            .then(|| runtime.replace_current_execution_mode(ExecutionMode::Trusted));
        let result = match if options.trust_before_line.is_some() {
            execute_top_level_statement_in_trusted_prefix_run(&stmt, runtime)
        } else {
            execute_top_level_statement(&stmt, runtime)
        } {
            Ok(result) => result,
            Err(error) => {
                if let Some(previous_execution_mode) = previous_execution_mode {
                    runtime.replace_current_execution_mode(previous_execution_mode);
                }
                return SourceRunOutcome::failure(stmt_results, error, execution_failure_kind);
            }
        };
        if let Some(previous_execution_mode) = previous_execution_mode {
            runtime.replace_current_execution_mode(previous_execution_mode);
        }
        if let Some(statement_start) = statement_start {
            let line_file = stmt.line_file();
            eprintln!(
                "repository statement {}:{}: {:.2} ms",
                line_file.1,
                line_file.0,
                statement_start.elapsed().as_secs_f64() * 1000.0,
            );
        }
        stmt_results.push(result);
    }

    SourceRunOutcome::success(stmt_results)
}

pub(super) fn trusted_prefix_boundary_error_message(
    file: &str,
    before_line: usize,
    statement_lines: &[usize],
) -> String {
    let previous = statement_lines
        .iter()
        .copied()
        .filter(|line| *line < before_line)
        .max();
    let next = statement_lines
        .iter()
        .copied()
        .filter(|line| *line > before_line)
        .min();
    let mut nearby = Vec::new();
    if let Some(previous) = previous {
        nearby.push(format!(
            "previous top-level statement starts at line {}",
            previous
        ));
    }
    if let Some(next) = next {
        nearby.push(format!("next top-level statement starts at line {}", next));
    }
    let nearby = if nearby.is_empty() {
        "the file has no top-level statements".to_string()
    } else {
        nearby.join("; ")
    };
    format!(
        "-trust-before-line {} must be the header line of a top-level statement in `{}`; {}",
        before_line, file, nearby
    )
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/source_execution/source_run_tests.rs"]
mod source_run_tests;
