use crate::error::RuntimeError;
use crate::result::StmtResult;
use crate::runtime::{Runtime, TrustedOrRequireVerify};
use crate::statement::Stmt;

impl Runtime {
    pub fn execute_statement(&mut self, stmt: &Stmt) -> Result<StmtResult, RuntimeError> {
        let execution_mode = self.current_execution_mode();
        match execution_mode {
            TrustedOrRequireVerify::Trusted => self.execute_statement_with_trust(stmt),
            TrustedOrRequireVerify::RequireVerification => {
                self.execute_statement_with_verification(stmt)
            }
        }
    }
}
