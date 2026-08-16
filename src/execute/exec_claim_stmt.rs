use crate::prelude::*;

impl Runtime {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<StmtResult, RuntimeError> {
        let result =
            self.exec_checked_goal_block(stmt.clone().into(), &stmt.fact, &stmt.proof, CLAIM)?;
        let infer_result_after_store = self.exec_claim_stmt_affect_environment(stmt)?;

        Ok(result.with_infers(infer_result_after_store))
    }

    pub(crate) fn exec_claim_stmt_affect_environment(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<InferResult, RuntimeError> {
        if self.current_execution_is_trusted_file() {
            return self.store_trusted_fact_and_infer_with_reason(
                stmt.fact.clone(),
                InferReason::ProvedClaim,
            );
        }

        self.store_without_well_defined_verification_and_infer_with_reason(
            stmt.fact.clone(),
            InferReason::ProvedClaim,
        )
    }

    pub(crate) fn exec_claim_stmt_affect_environment_only(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_claim_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}
