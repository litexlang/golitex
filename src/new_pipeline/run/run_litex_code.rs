use crate::new_pipeline::runtime::{RuntimeResult, Runtime};
use crate::new_pipeline::tokenize::Tokenizer;

impl Runtime {
    /// Tokenize → parse → exec one source string.
    pub fn run_litex_code(&mut self, code: &str) -> RuntimeResult<()> {
        let token_blocks = Tokenizer::new().tokenize(code, self.current_file.clone())?;
        let stmts = self.parse(&token_blocks)?;
        for stmt in &stmts {
            let _result = self.exec_stmt(stmt)?;
        }
        Ok(())
    }
}
