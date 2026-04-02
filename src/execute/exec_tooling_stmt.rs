use crate::prelude::*;

impl Runtime {
    pub fn exec_import_stmt(
        &mut self,
        stmt: &ImportStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            Stmt::ImportStmt(stmt.clone()),
            "".to_string(),
            None,
            vec![],
        )));
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DoNothingStmt(stmt.clone()),
                InferResult::new(),
                vec![],
            ),
        ));
    }

    pub fn exec_run_file_stmt(
        &mut self,
        stmt: &RunFileStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            Stmt::RunFileStmt(stmt.clone()),
            "".to_string(),
            None,
            vec![],
        )));
    }
}
