use super::run_command_outcome::{RunLitexCodeResult, RunSessionError};
use crate::execute::ExecStmtResult;
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::{TokenBlock, Tokenizer};

impl Runtime {
    /// Tokenize the source, then parse → exec each complete top-level block.
    /// Soft Failed rolls back parse bindings and continues (`success: false`).
    /// Parse/exec errors stop with prefix results and `session_error`, still `Ok`.
    /// Tokenization errors occur before execution and return `Err`.
    pub fn run_litex_code(&mut self, code: &str) -> RuntimeResult<RunLitexCodeResult> {
        let token_blocks = Tokenizer::new().tokenize(code, self.current_file.clone())?;
        let mut statement_results = Vec::new();
        let mut statement_texts = Vec::new();
        let mut session_error = None;

        for block in &token_blocks {
            // Finish execution and commit/rollback before parsing the next
            // block. Future declarations must not reserve names or affect
            // file-root qualification while this statement is executing.
            match self.parse_and_exec_token_block(block) {
                Ok((statement, outcome)) => {
                    statement_texts.push(statement);
                    statement_results.push(outcome);
                }
                Err(cause) => {
                    session_error = Some(RunSessionError::Runtime(cause));
                    break;
                }
            }
        }

        let mut result = RunLitexCodeResult::new(statement_results, session_error);
        result.statement_texts = statement_texts;
        Ok(result)
    }

    fn parse_and_exec_token_block(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<(String, ExecStmtResult)> {
        // Parsing reserves names; commit them only after execution succeeds.
        let ((statement, outcome), temporary_scopes) = self
            .run_in_temporary_parse_scopes_and_take_scopes(|runtime| {
                // Parse the complete proof AST before any nested execution.
                let stmt = runtime.parse_token_block(block)?;
                let statement = stmt.readable_string();
                let outcome = runtime.exec_stmt(&stmt)?;
                Ok((statement, outcome))
            })?;

        if outcome.is_failed() {
            return Ok((statement, outcome));
        }

        self.parse_scope_stack = temporary_scopes;
        Ok((statement, outcome))
    }
}
