use crate::prelude::*;

impl Runtime {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<StmtResult, RuntimeError> {
        let verification =
            self.verify_checked_goal_block(stmt.clone().into(), &stmt.fact, &stmt.proof, CLAIM)?;
        let environment_effects = self.exec_claim_stmt_affect_environment(stmt)?;

        Ok(
            SuccessProofBlockStmtResult::ClaimStmt(Box::new(SuccessClaimStmtResult::checked(
                stmt.clone(),
                verification,
                environment_effects,
            )))
            .into(),
        )
    }

    pub fn exec_claim_stmt_affect_environment(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        if self.current_execution_is_trusted_source() {
            return self.store_fact_with_trust_and_infer_with_reason(
                stmt.fact.clone(),
                InferReason::ProvedClaim,
            );
        }

        self.store_without_well_defined_verification_and_infer_with_reason(
            stmt.fact.clone(),
            InferReason::ProvedClaim,
        )
    }

    pub fn exec_claim_stmt_affect_environment_only(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_claim_stmt_affect_environment(stmt)?;
        Ok(
            SuccessProofBlockStmtResult::ClaimStmt(Box::new(SuccessClaimStmtResult::with_trust(
                stmt.clone(),
                infer_result,
            )))
            .into(),
        )
    }
}
