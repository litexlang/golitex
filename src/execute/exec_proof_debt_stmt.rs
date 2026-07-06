use crate::prelude::*;

impl Runtime {
    pub fn exec_proof_debt_stmt(
        &mut self,
        proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<StmtResult, RuntimeError> {
        if self.strict_mode {
            return Err(short_exec_error(
                proof_debt_stmt.clone().into(),
                ProofDebtStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }

        let mut infer_result = InferResult::new();
        for fact in proof_debt_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer_with_reason(
                    fact.clone(),
                    &VerifyState::new(0, false),
                    InferReason::UnsafeAssumption,
                )
                .map_err(|e| {
                    exec_stmt_error_with_stmt_and_cause(proof_debt_stmt.clone().into(), e)
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(
            (NonFactualStmtSuccess::new(proof_debt_stmt.clone().into(), infer_result, vec![]))
                .into(),
        )
    }
}
