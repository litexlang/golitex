use crate::prelude::*;
use crate::new_pipeline::runtime::Runtime;

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> Result<ExecStmtResult2, RuntimeError> {
        let _ = stmt;
        unimplemented!("new_pipeline exec_stmt")
    }
}
