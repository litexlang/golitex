use super::run_command_outcome::{RunInputError, RunLitexCodeResult, RunSessionError};
use super::source_observer::SourceObserver;
use crate::execute::ExecStmtResult;
use crate::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::tokenize::{TokenBlock, Tokenizer};

impl Runtime {
    /// Tokenize the source, then parse → exec each complete top-level block.
    /// Soft Failed rolls back parse bindings and continues (`success: false`).
    /// Invalid input stops this submission with `input_error`, retaining context.
    /// Hard execution errors stop with prefix results and `session_error`.
    pub fn run_litex_code(&mut self, code: &str) -> RuntimeResult<RunLitexCodeResult> {
        self.run_litex_code_observed(code, &mut ())
    }

    pub fn run_litex_code_observed(
        &mut self,
        code: &str,
        observer: &mut dyn SourceObserver,
    ) -> RuntimeResult<RunLitexCodeResult> {
        observer.source(self, code);
        let token_blocks = match Tokenizer::new().tokenize(code, self.current_file.clone()) {
            Ok(blocks) => blocks,
            Err(error) => {
                observer.source_error(self, &error);
                let RuntimeError::ParseError(error) = error else {
                    return Err(error);
                };
                let mut result = RunLitexCodeResult::new(Vec::new(), None);
                result.success = false;
                result.input_error = Some(RunInputError::new(code.trim_end().to_string(), error));
                observer.completed(self, &result);
                return Ok(result);
            }
        };
        let mut statement_results = Vec::new();
        let mut statement_texts = Vec::new();
        let mut session_error = None;
        let mut input_error = None;

        for (index, block) in token_blocks.iter().enumerate() {
            // Finish execution and commit/rollback before parsing the next
            // block. Future declarations must not reserve names or affect
            // file-root qualification while this statement is executing.
            match self.parse_and_exec_token_block(block, observer) {
                Ok((statement, outcome)) => {
                    statement_texts.push(statement);
                    statement_results.push(outcome);
                }
                Err(cause) => {
                    if let RuntimeError::ParseError(error) = cause {
                        let end = token_blocks
                            .get(index + 1)
                            .map(|next| next.line - 1)
                            .unwrap_or_else(|| code.lines().count());
                        let statement = code
                            .lines()
                            .skip(block.line - 1)
                            .take(end - (block.line - 1))
                            .collect::<Vec<_>>()
                            .join("\n");
                        observer.source_error(self, &RuntimeError::ParseError(error.clone()));
                        input_error =
                            Some(RunInputError::new(statement.trim_end().to_string(), error));
                    } else {
                        session_error = Some(RunSessionError::Runtime(cause));
                    }
                    break;
                }
            }
        }

        let mut result = RunLitexCodeResult::new(statement_results, session_error);
        result.statement_texts = statement_texts;
        if input_error.is_some() {
            result.success = false;
        }
        result.input_error = input_error;
        observer.completed(self, &result);
        Ok(result)
    }

    fn parse_and_exec_token_block(
        &mut self,
        block: &TokenBlock,
        observer: &mut dyn SourceObserver,
    ) -> RuntimeResult<(String, ExecStmtResult)> {
        // Parsing reserves names; commit them only after execution succeeds.
        let ((statement, outcome), temporary_scopes) = self
            .run_in_temporary_parse_scopes_and_take_scopes(|runtime| {
                // Parse the complete proof AST before any nested execution.
                let stmt = runtime.parse_token_block(block)?;
                let statement = stmt.readable_string();
                let outcome = runtime.exec_stmt(&stmt)?;
                observer.statement(runtime, block, &stmt, &outcome);
                Ok((statement, outcome))
            })?;

        if outcome.is_failed() {
            return Ok((statement, outcome));
        }

        self.parse_scope_stack = temporary_scopes;
        Ok((statement, outcome))
    }
}
