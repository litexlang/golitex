use crate::prelude::*;

impl Runtime {
    pub fn exec_know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<StmtResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for fact in know_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(
                    fact.clone(),
                    &VerifyState::new(0, false),
                )
                .map_err(|e| short_exec_error(know_stmt.clone().into(), "", Some(e), vec![]))?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok((NonFactualStmtSuccess::new(know_stmt.clone().into(), infer_result, vec![])).into())
    }
}
