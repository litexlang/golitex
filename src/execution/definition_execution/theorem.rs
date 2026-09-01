use crate::prelude::*;

impl Runtime {
    pub fn exec_def_thm_stmt(&mut self, stmt: &DefThmStmt) -> Result<StmtResult, RuntimeError> {
        let label = format!("thm `{}`", stmt.name);
        let verification = self.verify_checked_goal_block(
            stmt.clone().into(),
            &stmt.fact,
            &stmt.prove_process,
            &label,
        )?;
        let infer_result = self.exec_def_thm_stmt_affect_environment(stmt)?;
        let source_fact_id = self.require_known_fact_id_for_success_result(&stmt.fact)?;
        let theorem_verification = SuccessVerifyTheoremResult::new(
            stmt.name.clone(),
            verification.fact,
            verification.well_definedness,
            verification.domain,
            verification.proof_steps,
            verification.conclusion_checks,
        );

        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(Box::new(
                SuccessDefThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    source_fact_id,
                    verification: Some(theorem_verification),
                },
            )))
            .into(),
        )
    }

    pub fn exec_def_thm_stmt_affect_environment(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_def_thm(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        if self.current_execution_is_trusted_file() {
            return self.store_fact_with_trust_and_infer_with_reason(
                stmt.fact.clone(),
                InferReason::Other(stmt.store_reason().to_string()),
            );
        }

        self.store_without_well_defined_verification_and_infer_with_reason(
            stmt.fact.clone(),
            InferReason::Other(stmt.store_reason().to_string()),
        )
    }

    pub fn exec_def_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_def_thm_stmt_affect_environment(stmt)?;
        let source_fact_id = self.require_known_fact_id_for_success_result(&stmt.fact)?;
        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(Box::new(
                SuccessDefThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    source_fact_id,
                    verification: None,
                },
            )))
            .into(),
        )
    }
}
