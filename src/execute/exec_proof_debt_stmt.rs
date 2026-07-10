use crate::prelude::*;

impl Runtime {
    pub fn exec_proof_debt_stmt(
        &mut self,
        proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_proof_debt_stmt_verify_well_definedness(proof_debt_stmt)?;
        self.exec_proof_debt_stmt_verify_process(proof_debt_stmt)?;
        let infer_result = self.exec_proof_debt_stmt_affect_environment(proof_debt_stmt)?;
        Ok(NonFactualStmtSuccess::new(proof_debt_stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_proof_debt_stmt_verify_well_definedness(
        &mut self,
        _proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_proof_debt_stmt_verify_process(
        &mut self,
        proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        if self.strict_mode_applies_to_current_module() {
            return Err(short_exec_error(
                proof_debt_stmt.clone().into(),
                ProofDebtStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }
        Ok(vec![])
    }

    pub(crate) fn exec_proof_debt_stmt_affect_environment(
        &mut self,
        proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for fact in proof_debt_stmt.facts.iter() {
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
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(proof_debt_stmt.clone().into(), e))?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(infer_result)
    }

    pub(crate) fn exec_proof_debt_stmt_affect_environment_only(
        &mut self,
        proof_debt_stmt: &ProofDebtStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_proof_debt_stmt_affect_environment(proof_debt_stmt)?;
        Ok(NonFactualStmtSuccess::new(proof_debt_stmt.clone().into(), infer_result, vec![]).into())
    }
}
