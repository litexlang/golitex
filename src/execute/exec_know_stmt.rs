use crate::prelude::*;

impl Runtime {
    pub fn exec_know_stmt(
        &mut self,
        know_stmt: &KnowStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeErrorStruct> {
        let mut infer_result = InferResult::new();
        for fact in know_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(
                    fact.clone(),
                    &VerifyState::new(0, false),
                )
                .map_err(|e| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        Stmt::KnowStmt(know_stmt.clone()),
                        "".to_string(),
                        Some(e.into()),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(Stmt::KnowStmt(know_stmt.clone()), infer_result, vec![]),
        ))
    }
}
