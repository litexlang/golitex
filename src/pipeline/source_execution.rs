use crate::common::keywords::TRY;
use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct, UnknownRuntimeError};
use crate::parse::{TokenBlock, Tokenizer};
use crate::result::StmtResult;
use crate::runtime::Runtime;
use crate::stmt::{CommandStmt, ProofBlockStmt, Stmt};

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

    pub fn into_parts(self) -> (Vec<StmtResult>, Option<RuntimeError>) {
        (self.stmt_results, self.runtime_error)
    }
}

impl Runtime {
    pub fn execute_source(
        &mut self,
        source_code: &str,
        import_policy: SourceImportPolicy,
    ) -> SourceRunOutcome {
        if !self.has_active_execution_frame() {
            let error = ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "runtime has no active source context; initialize a file or repository before running source"
                    .to_string(),
            ))
            .into();
            return SourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
        }

        let blocks = match tokenize_source_code(source_code, self) {
            Ok(blocks) => blocks,
            Err((error, failure_kind)) => {
                return SourceRunOutcome::failure(vec![], error, failure_kind);
            }
        };

        self.execute_source_blocks(blocks, &import_policy)
    }

    fn execute_source_blocks(
        &mut self,
        blocks: Vec<TokenBlock>,
        import_policy: &SourceImportPolicy,
    ) -> SourceRunOutcome {
        let mut stmt_results: Vec<StmtResult> = Vec::new();
        for mut block in blocks {
            let parse_failure_kind = if block.current_token_is_equal_to(TRY) {
                SourceRunFailureKind::TryStmt
            } else {
                SourceRunFailureKind::Other
            };
            let stmt = match self.parse_statement(&mut block) {
                Ok(stmt) => stmt,
                Err(error) => {
                    return SourceRunOutcome::failure(stmt_results, error, parse_failure_kind);
                }
            };
            if let (
                SourceImportPolicy::Reject(message),
                Stmt::Command(CommandStmt::ImportStmt(_)),
            ) = (import_policy, &stmt)
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
            let result = match self.execute_top_level_statement(&stmt) {
                Ok(result) => result,
                Err(error) => {
                    return SourceRunOutcome::failure(stmt_results, error, execution_failure_kind);
                }
            };
            stmt_results.push(result);
        }

        SourceRunOutcome::success(stmt_results)
    }
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

#[cfg(test)]
#[path = "../../tests/unit/pipeline/source_execution/source_run_tests.rs"]
mod source_run_tests;
