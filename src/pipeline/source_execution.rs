use crate::error::{ParseRuntimeError, RuntimeError, RuntimeErrorStruct};
use crate::parsing::{TokenBlock, Tokenizer};
use crate::result::StmtResult;
use crate::runtime::Runtime;
use crate::statement::{ProofBlockStmt, Stmt};
use crate::syntax::keywords::TRY;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SourceRunFailureKind {
    TryStmt,
    Other,
}

pub struct SourceRunOutcome {
    pub stmt_results: Vec<StmtResult>,
    pub runtime_error: Option<RuntimeError>,
}

impl SourceRunOutcome {
    fn success(stmt_results: Vec<StmtResult>) -> Self {
        Self {
            stmt_results,
            runtime_error: None,
        }
    }

    fn failure(stmt_results: Vec<StmtResult>, runtime_error: RuntimeError) -> Self {
        Self {
            stmt_results,
            runtime_error: Some(runtime_error),
        }
    }

    pub fn into_parts(self) -> (Vec<StmtResult>, Option<RuntimeError>) {
        (self.stmt_results, self.runtime_error)
    }
}

pub(super) struct ClassifiedSourceRunOutcome {
    outcome: SourceRunOutcome,
    failure_kind: Option<SourceRunFailureKind>,
}

impl ClassifiedSourceRunOutcome {
    fn success(stmt_results: Vec<StmtResult>) -> Self {
        Self {
            outcome: SourceRunOutcome::success(stmt_results),
            failure_kind: None,
        }
    }

    fn failure(
        stmt_results: Vec<StmtResult>,
        runtime_error: RuntimeError,
        failure_kind: SourceRunFailureKind,
    ) -> Self {
        Self {
            outcome: SourceRunOutcome::failure(stmt_results, runtime_error),
            failure_kind: Some(failure_kind),
        }
    }

    pub(super) fn into_parts(self) -> (SourceRunOutcome, Option<SourceRunFailureKind>) {
        (self.outcome, self.failure_kind)
    }
}

impl Runtime {
    pub fn execute_source(&mut self, source_code: &str) -> SourceRunOutcome {
        self.execute_source_classified(source_code).outcome
    }

    pub(super) fn execute_source_classified(
        &mut self,
        source_code: &str,
    ) -> ClassifiedSourceRunOutcome {
        if !self.has_active_execution_frame() {
            let error = ParseRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                "runtime has no active source context; initialize a file or repository before running source"
                    .to_string(),
            ))
            .into();
            return ClassifiedSourceRunOutcome::failure(vec![], error, SourceRunFailureKind::Other);
        }

        let blocks = match tokenize_source_code(source_code, self) {
            Ok(blocks) => blocks,
            Err((error, failure_kind)) => {
                return ClassifiedSourceRunOutcome::failure(vec![], error, failure_kind);
            }
        };

        self.execute_source_blocks(blocks)
    }

    fn execute_source_blocks(&mut self, blocks: Vec<TokenBlock>) -> ClassifiedSourceRunOutcome {
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
                    return ClassifiedSourceRunOutcome::failure(
                        stmt_results,
                        error,
                        parse_failure_kind,
                    );
                }
            };
            let execution_failure_kind =
                if matches!(&stmt, Stmt::ProofBlock(ProofBlockStmt::TryStmt(_))) {
                    SourceRunFailureKind::TryStmt
                } else {
                    SourceRunFailureKind::Other
                };
            let result = match self.execute_statement(&stmt) {
                Ok(result) => result,
                Err(error) => {
                    return ClassifiedSourceRunOutcome::failure(
                        stmt_results,
                        error,
                        execution_failure_kind,
                    );
                }
            };
            stmt_results.push(result);
        }

        ClassifiedSourceRunOutcome::success(stmt_results)
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
