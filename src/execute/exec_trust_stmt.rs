use crate::prelude::*;

impl Runtime {
    pub fn exec_trust_stmt(&mut self, trust_stmt: &TrustStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_trust_stmt_verify_well_definedness(trust_stmt)?;
        self.exec_trust_stmt_verify_process(trust_stmt)?;
        let infer_result = self.exec_trust_stmt_affect_environment(trust_stmt)?;
        Ok(NonFactualStmtSuccess::new(trust_stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_trust_stmt_verify_well_definedness(
        &mut self,
        _trust_stmt: &TrustStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_trust_stmt_verify_process(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                trust_stmt.clone().into(),
                TrustStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }
        Ok(vec![])
    }

    pub(crate) fn exec_trust_stmt_affect_environment(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for fact in trust_stmt.facts.iter() {
            let fact_infer_result = if self.current_execution_is_trusted_file() {
                self.store_trusted_fact_and_infer_with_reason(
                    fact.clone(),
                    InferReason::UnsafeAssumption,
                )
            } else {
                self.verify_fact_well_defined_and_store_and_infer_with_reason(
                    fact.clone(),
                    &VerifyState::new(0, false),
                    InferReason::UnsafeAssumption,
                )
            }
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(trust_stmt.clone().into(), e))?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub(crate) fn exec_trust_stmt_affect_environment_only(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_trust_stmt_affect_environment(trust_stmt)?;
        Ok(NonFactualStmtSuccess::new(trust_stmt.clone().into(), infer_result, vec![]).into())
    }
}
