use crate::prelude::*;

impl Runtime {
    pub fn exec_trust_stmt(&mut self, trust_stmt: &TrustStmt) -> Result<StmtResult, RuntimeError> {
        self.reject_trust_stmt_in_strict_mode(trust_stmt)?;
        self.exec_trust_stmt_affect_environment_only(trust_stmt)
    }

    fn reject_trust_stmt_in_strict_mode(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<(), RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                trust_stmt.clone().into(),
                TrustStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }
        Ok(())
    }

    /// Mathematical contract implementation: `trust` skips both WD and truth
    /// verification. All facts and their inferred consequences are committed
    /// atomically after the strict-mode gate.
    fn exec_trust_stmt_affect_environment(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = SuccessInferResult::new();
        for fact in trust_stmt.facts.iter() {
            let fact_infer_result = self
                .store_fact_with_trust_and_infer_with_reason(
                    fact.clone(),
                    InferReason::UnsafeAssumption,
                )
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(trust_stmt.clone().into(), e))?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub fn exec_trust_stmt_affect_environment_only(
        &mut self,
        trust_stmt: &TrustStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env_and_commit(|rt| {
            let mut infer_result = rt.exec_trust_stmt_affect_environment(trust_stmt)?;
            // Freeze every assumption-local identity while the producing
            // environment is still present. Quantified facts can lose their
            // cache lookup route after this child scope is merged.
            rt.attach_known_fact_ids_to_infer_result(&mut infer_result)?;
            Ok(
                SuccessUnsafeStmtResult::TrustStmt(Box::new(SuccessTrustStmtResult {
                    statement: trust_stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                }))
                .into(),
            )
        })
    }
}
