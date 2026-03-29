use crate::prelude::*;

impl Runtime {
    fn exec_claim_stmt_body_fact_for_forall_fact(
        &mut self,
        stmt: &ClaimStmt,
        forall_fact: &ForallFact,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.define_params_with_type(
            &forall_fact.params_def_with_type,
            false,
        )
        .map_err(|define_params_error| {
            ExecStmtError::new(
                Stmt::ClaimStmt(stmt.clone()),
                "".to_string(),
                Some(define_params_error.into()),
                vec![],
            )
        })?;

        for dom_fact in forall_fact.dom_facts.iter() {
            self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                dom_fact,
            )?;
        }

        let mut inside_results = vec![];
        for proof_stmt in stmt.proof.iter() {
            let result = self.exec_stmt(proof_stmt)?;
            inside_results.push(result);
        }

        for then_fact in forall_fact.then_facts.iter() {
            let result =
                self.verify_exist_or_and_chain_atomic_fact(then_fact, &VerifyState::new(0, false))?;
            if result.is_unknown() {
                return Err(RuntimeError::UnknownError(UnknownError::new(
                    format!("claim failed: cannot prove `{}`", stmt.fact),
                    stmt.line_file,
                    None,
                )));
            }

            inside_results.push(result);
        }

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ClaimStmt(stmt.clone()),
                crate::infer::InferResult::new(),
                inside_results,
            ),
        ))
    }

    fn exec_claim_stmt_body_fact_except_forall_fact(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in stmt.proof.iter() {
            let proof_exec_result = self.exec_stmt(proof_stmt)?;
            inside_results.push(proof_exec_result);
        }

        self.verify_fact_return_err_if_not_true(&stmt.fact, &VerifyState::new(0, false))?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ClaimStmt(stmt.clone()),
                crate::infer::InferResult::new(),
                inside_results,
            ),
        ))
    }

    pub fn exec_claim_stmt(
        &mut self,
        stmt: &ClaimStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(forall_fact) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                            Stmt::ClaimStmt(stmt.clone()),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            vec![],
                        ))
                    })?;

                self.push_env();
                let body_exec_result =
                    self.exec_claim_stmt_body_fact_for_forall_fact(stmt, forall_fact);
                self.pop_env();

                let non_err_after_body = match body_exec_result {
                    Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
                    Err(runtime_error) => return Err(runtime_error),
                };
                if non_err_after_body.is_unknown() {
                    return Err(RuntimeError::UnknownError(UnknownError::new(
                        format!("claim failed: cannot prove `{}`", stmt.fact),
                        stmt.line_file,
                        None,
                    )));
                }

                let infer_result_after_store =
                    self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
            _ => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                            Stmt::ClaimStmt(stmt.clone()),
                            "claim: fact is not well defined".to_string(),
                            Some(e.into()),
                            vec![],
                        ))
                    })?;

                self.push_env();
                let body_exec_result = self.exec_claim_stmt_body_fact_except_forall_fact(stmt);
                self.pop_env();

                let non_err_after_body = match body_exec_result {
                    Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
                    Err(runtime_error) => return Err(runtime_error),
                };
                let infer_result_after_store =
                    self.store_fact_without_well_defined_verified_and_infer(&stmt.fact)?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
        }
    }
}
