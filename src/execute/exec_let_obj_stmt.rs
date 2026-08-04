use crate::prelude::*;

impl Runtime {
    pub fn exec_let_obj_stmt(&mut self, stmt: &LetObjStmt) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(
            &stmt.value,
            &UseContextVerifyState::new(0, false),
        )
        .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        let infer_result = self.exec_let_obj_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_let_obj_stmt_affect_environment(
        &mut self,
        stmt: &LetObjStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
            .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))?;

        let equal_fact: AtomicFact = EqualFact::new(
            Identifier::new_bound(
                stmt.symbol_binding.name().to_string(),
                stmt.symbol_binding.as_ref(),
            )
            .into(),
            stmt.value.clone(),
            stmt.line_file.clone(),
        )
        .into();
        self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
            equal_fact,
            LetObjStmt::store_reason(),
        )
        .map_err(|error| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), error))
    }

    pub(crate) fn exec_let_obj_stmt_affect_environment_only(
        &mut self,
        stmt: &LetObjStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_let_obj_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}
