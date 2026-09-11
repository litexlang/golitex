use crate::new_pipeline::runtime::{PipelineResult, Runtime};
use crate::new_pipeline::tokenize::Tokenizer;

impl Runtime {
    /// Tokenize → parse → exec one source string.
    pub fn run_litex_code(&mut self, code: &str) -> PipelineResult<()> {
        let source_path = self.current_file.display_path();
        let token_blocks = Tokenizer::new().tokenize(code, source_path)?;
        let stmts = self.parse(&token_blocks)?;
        for stmt in &stmts {
            self.exec_stmt(stmt)?;
        }
        Ok(())
    }
}
