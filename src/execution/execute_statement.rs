use crate::error::RuntimeError;
use crate::result::StmtResult;
use crate::runtime::{ExecutionMode, Runtime};
use crate::statement::Stmt;

impl Runtime {
    pub fn execute_statement(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        self.mark_source_execution_started();
        let execution_mode = self.current_execution_mode();
        match execution_mode {
            ExecutionMode::Trusted => self.execute_statement_with_trust(stmt),
            ExecutionMode::RequireVerification => self.execute_statement_with_verification(stmt),
        }
    }
}
