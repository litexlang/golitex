use crate::prelude::*;

impl Runtime {
    pub fn exec_know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<StmtResult, RuntimeError> {
        if self.strict_mode {
            return Err(short_exec_error(
                know_stmt.clone().into(),
                KnowStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }

        let mut infer_result = InferResult::new();
        for fact in know_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer_with_reason(
                    fact.clone(),
                    &VerifyState::new(0, false),
                    InferReason::UnsafeAssumption,
                )
                .map_err(|e| exec_stmt_error_with_stmt_and_cause(know_stmt.clone().into(), e))?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok((NonFactualStmtSuccess::new(know_stmt.clone().into(), infer_result, vec![])).into())
    }
}
