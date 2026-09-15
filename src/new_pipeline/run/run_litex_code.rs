use crate::new_pipeline::execute::ExecStmtResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::new_pipeline::tokenize::Tokenizer;

impl Runtime {
    /// Tokenize → parse → exec one source string.
    /// Soft Fail stops the file run (maps to Err) without polluting parent env;
    /// hard Err is SessionError.
    pub fn run_litex_code(&mut self, code: &str) -> RuntimeResult<()> {
        let token_blocks = Tokenizer::new().tokenize(code, self.current_file.clone())?;
        let stmts = self.parse(&token_blocks)?;
        for stmt in &stmts {
            match self.exec_stmt(stmt)? {
                ExecStmtResult::Success(_) => {}
                ExecStmtResult::Failed(_) => {
                    return Err(RuntimeError::Unknown(
                        "statement failed (soft miss); file run stopped".to_string(),
                    ));
                }
            }
        }
        Ok(())
    }
}
