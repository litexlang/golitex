use crate::error::RuntimeError;
use crate::parsing::{TokenBlock, Tokenizer};
use crate::result::StmtResult;
use crate::runtime::Runtime;

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

impl Runtime {
    pub fn execute_source(&mut self, source_code: &str) -> SourceRunOutcome {
        let blocks = match tokenize_source_code(source_code, self) {
            Ok(blocks) => blocks,
            Err(error) => {
                return SourceRunOutcome::failure(vec![], error);
            }
        };

        self.execute_source_blocks(blocks)
    }

    fn execute_source_blocks(&mut self, blocks: Vec<TokenBlock>) -> SourceRunOutcome {
        let mut stmt_results: Vec<StmtResult> = Vec::new();
        for mut block in blocks {
            let stmt = match self.parse_statement(&mut block) {
                Ok(stmt) => stmt,
                Err(error) => {
                    return SourceRunOutcome::failure(stmt_results, error);
                }
            };
            let result = match self.execute_statement(&stmt) {
                Ok(result) => result,
                Err(error) => {
                    return SourceRunOutcome::failure(stmt_results, error);
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
) -> Result<Vec<TokenBlock>, RuntimeError> {
    Tokenizer::new().parse_blocks(source_code, runtime.current_file_path_rc())
}

#[cfg(test)]
#[path = "../../tests/unit/pipeline/source_execution/source_run_tests.rs"]
mod source_run_tests;
