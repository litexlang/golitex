use crate::prelude::*;

impl Runtime {
    pub fn exec_do_nothing_stmt(
        &mut self,
        stmt: &DoNothingStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_do_nothing_stmt_verify_well_definedness(stmt)?;
        self.exec_do_nothing_stmt_verify_process(stmt)?;
        let infer_result = self.exec_do_nothing_stmt_affect_environment(stmt)?;
        Ok(
            SuccessCommandStmtResult::DoNothingStmt(Box::new(SuccessDoNothingStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
            }))
            .into(),
        )
    }

    pub fn exec_clear_stmt(&mut self, stmt: &ClearStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_clear_stmt_verify_well_definedness(stmt)?;
        self.exec_clear_stmt_verify_process(stmt)?;
        let infer_result = self.exec_clear_stmt_affect_environment(stmt)?;
        Ok(
            SuccessCommandStmtResult::ClearStmt(Box::new(SuccessClearStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
            }))
            .into(),
        )
    }

    /// Mathematical contract: a no-op statement contains no mathematical
    /// object or fact and is therefore vacuously well-defined.
    fn exec_do_nothing_stmt_verify_well_definedness(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_do_nothing_stmt_verify_process(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_do_nothing_stmt_affect_environment(
        &mut self,
        _stmt: &DoNothingStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        Ok(SuccessInferResult::new())
    }

    /// Mathematical contract: `clear` is an environment operation with no
    /// mathematical expression to type or define.
    fn exec_clear_stmt_verify_well_definedness(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_clear_stmt_verify_process(&mut self, _stmt: &ClearStmt) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_clear_stmt_affect_environment(
        &mut self,
        _stmt: &ClearStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.clear_current_env_and_parse_name_scope();
        Ok(SuccessInferResult::new())
    }
}
