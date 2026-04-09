use crate::prelude::*;

impl Runtime {
    pub fn exec_import_stmt(
        &mut self,
        stmt: &ImportStmt,
    ) -> Result<StmtExecResult, RuntimeError> {
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
    ) -> Result<StmtExecResult, RuntimeError> {
        return Ok(StmtExecResult::NonFactualStmtSuccess(
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
    ) -> Result<StmtExecResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            Stmt::RunFileStmt(stmt.clone()),
            "".to_string(),
            None,
            vec![],
        )));
    }
}
