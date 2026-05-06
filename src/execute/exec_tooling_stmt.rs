use crate::prelude::*;

impl Runtime {
    pub fn exec_import_stmt(&mut self, stmt: &ImportStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let st: Stmt = stmt.clone().into();
            let lf = st.line_file();
            RuntimeErrorStruct::new(Some(st), "".to_string(), lf, None, vec![])
        }));
    }

    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        return Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into());
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<StmtResult, RuntimeError> {
        self.clear_current_env_and_parse_name_scope();
        Ok(NonFactualStmtSuccess::new_with_stmt(stmt.clone().into()).into())
    }

    pub fn exec_run_file_stmt(&mut self, stmt: &RunFileStmt) -> Result<StmtResult, RuntimeError> {
        return Err(RuntimeError::ExecStmtError({
            let st: Stmt = stmt.clone().into();
            let lf = st.line_file();
            RuntimeErrorStruct::new(Some(st), "".to_string(), lf, None, vec![])
        }));
    }
}
