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
        // A continued REPL shares the file environment, but its new input has
        // interactive provenance rather than the original file's source path.
        let source_path = if self.code_source == crate::runtime::CodeSource::Repl {
            crate::runtime::RealOrVirtualPath::Repl
        } else {
            self.current_file.clone()
        };
        let token_blocks = Tokenizer::new().tokenize(code, source_path)?;
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
        // The transaction begins BEFORE parse, because parse itself occupies
        // names. Parse success alone cannot commit them: exec_stmt may still
        // reject the declaration and discard its temporary execution env.
        let scopes_before = self.begin_parse_scope_transaction();
        // A claim/thm includes its entire proof AST. Nothing nested executes
        // until this complete top-level block has parsed successfully.
        let result = self.parse_token_block(block).and_then(|stmt| {
            let statement = stmt.readable_string();
            self.exec_stmt(&stmt).map(|outcome| (statement, outcome))
        });

        match result {
            Ok((statement, outcome)) if !outcome.is_failed() => Ok((statement, outcome)),
            failed_or_error => {
                // Discard speculative parse names on soft failure AND errors.
                // Prior successful blocks and global ID counters stay intact.
                self.parse_scope_stack = scopes_before;
                failed_or_error
            }
        }
    }
}
