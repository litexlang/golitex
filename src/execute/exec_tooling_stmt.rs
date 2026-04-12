use crate::prelude::*;

impl Runtime {
    pub fn exec_import_stmt(
        &mut self,
        stmt: &ImportStmt,
    ) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            stmt.clone().into(),
            "".to_string(),
            None,
            vec![],
        )));
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        return Ok((NonFactualStmtSuccess::new(
                stmt.clone().into(),
                InferResult::new(),
                vec![],
            )).into());
    }

    pub fn exec_run_file_stmt(
        &mut self,
        stmt: &RunFileStmt,
    ) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::from(RuntimeErrorStruct::exec_stmt_new_with_stmt(
            stmt.clone().into(),
            "".to_string(),
            None,
            vec![],
        )));
    }
}
