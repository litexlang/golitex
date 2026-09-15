use super::run_command_outcome::{RunLitexCodeResult, RunSessionError};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::Tokenizer;

impl Runtime {
    /// Tokenize → parse → exec one source string.
    /// Soft Failed is kept in `statement_results` with `success: false`.
    /// Hard SessionError is kept in `session_error` with the successful prefix; still `Ok`.
    pub fn run_litex_code(&mut self, code: &str) -> RuntimeResult<RunLitexCodeResult> {
        let token_blocks = Tokenizer::new().tokenize(code, self.current_file.clone())?;
        let stmts = self.parse(&token_blocks)?;
        let mut statement_results = Vec::new();

        for stmt in &stmts {
            match self.exec_stmt(stmt) {
                Ok(outcome) => {
                    let failed = outcome.is_failed();
                    statement_results.push(outcome);
                    if failed {
                        return Ok(RunLitexCodeResult::new(statement_results, None));
                    }
                }
                Err(cause) => {
                    return Ok(RunLitexCodeResult::new(
                        statement_results,
                        Some(RunSessionError::Runtime(cause)),
                    ));
                }
            }
        }

        Ok(RunLitexCodeResult::new(statement_results, None))
    }
}
