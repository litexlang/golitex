use crate::prelude::*;

impl Runtime {
    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_do_nothing_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_do_nothing_stmt_verify_process(stmt)?;
        let infer_result = self.exec_do_nothing_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_clear_stmt_verify_well_definedness(stmt)?;
        let inside_results = self.exec_clear_stmt_verify_process(stmt)?;
        let infer_result = self.exec_clear_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }

    fn exec_do_nothing_stmt_verify_well_definedness(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_do_nothing_stmt_verify_process(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        Ok(vec![])
    }

    fn exec_do_nothing_stmt_affect_environment(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<InferResult, RuntimeError> {
        Ok(InferResult::new())
    }

    fn exec_clear_stmt_verify_well_definedness(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_clear_stmt_verify_process(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        Ok(vec![])
    }

    fn exec_clear_stmt_affect_environment(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.clear_current_env_and_parse_name_scope();
        Ok(InferResult::new())
    }
}
