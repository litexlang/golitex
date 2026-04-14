use crate::prelude::*;

impl Runtime {
    pub fn exec_import_stmt(&mut self, stmt: &ImportStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let __stmt: Stmt = stmt.clone().into();
            let __line_file = __stmt.line_file();
            RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, None, vec![])
        }));
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        return Ok(
            (NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), vec![])).into(),
        );
    }

    pub fn exec_run_file_stmt(&mut self, stmt: &RunFileStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let __stmt: Stmt = stmt.clone().into();
            let __line_file = __stmt.line_file();
            RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, None, vec![])
        }));
    }
}
