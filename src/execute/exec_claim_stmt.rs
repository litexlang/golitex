use crate::prelude::*;

impl Runtime {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<StmtResult, RuntimeError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(forall_fact) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        short_exec_error(
                            stmt.clone().into(),
                            "claim: fact is not well defined".to_string(),
                            Some(e),
                            vec![],
                        )
                    })?;

                let body_exec_result = self.run_in_local_env(|rt| {
                    let assumption_infers = rt.forall_assume_params_and_dom_in_current_env(
                        forall_fact,
                        &VerifyState::new(0, false),
                    )?;

                    let mut inside_results = vec![];
                    let proof_len = stmt.proof.len();
                    for (proof_index, proof_stmt) in stmt.proof.iter().enumerate() {
                        let result = rt.exec_stmt(proof_stmt)?;
                        if result.is_unknown() {
                            return Err(UnknownRuntimeError(RuntimeErrorStruct::new_with_output(
                                Some(proof_stmt.clone()),
                                "claim failed: proof step is unknown".to_string(),
                                proof_stmt.line_file(),
                                None,
                                vec![],
                                RuntimeErrorOutput::proof_step_unknown(
                                    proof_stmt.clone(),
                                    proof_index + 1,
                                    proof_len,
                                    &result,
                                ),
                            ))
                            .into());
                        }
                        inside_results.push(result);
                    }

                    let then_count = forall_fact.then_facts.len();
                    for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
                        let mut result = rt.verify_exist_or_and_chain_atomic_fact(
                            then_fact,
                            &VerifyState::new(0, false),
                        )?;
                        if result.is_unknown() {
                            let then_goal = then_fact.clone().to_fact();
                            result = result.wrap_unknown_for_fact(then_goal.clone());
                            return Err(UnknownRuntimeError(RuntimeErrorStruct::new_with_output(
                                Some(then_goal.clone().into()),
                                "claim failed: cannot prove then-clause".to_string(),
                                then_fact.line_file(),
                                None,
                                vec![],
                                RuntimeErrorOutput::then_clause_unknown(
                                    then_goal,
                                    then_index + 1,
                                    then_count,
                                    &result,
                                ),
                            ))
                            .into());
                        }
                        inside_results.push(result);
                    }

                    let claim_verification = ClaimForallVerificationResult::new(
                        forall_fact.clone(),
                        assumption_infers,
                        proof_len,
                    )
                    .into();

                    Ok(NonFactualStmtSuccess::new_with_claim_verification(
                        stmt.clone().into(),
                        InferResult::new(),
                        inside_results,
                        claim_verification,
                    )
                    .into())
                });

                let non_err_after_body: StmtResult = match body_exec_result {
                    Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
                    Err(runtime_error) => return Err(runtime_error),
                };
                if non_err_after_body.is_unknown() {
                    return Err(UnknownRuntimeError(RuntimeErrorStruct::new(
                        Some(stmt.clone().into()),
                        format!("claim failed: cannot prove `{}`", stmt.fact),
                        stmt.line_file.clone(),
                        None,
                        vec![],
                    ))
                    .into());
                }

                let infer_result_after_store = self
                    .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                        stmt.fact.clone(),
                        InferReason::ProvedClaim,
                    )?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
            _ => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        short_exec_error(
                            stmt.clone().into(),
                            "claim: fact is not well defined".to_string(),
                            Some(e),
                            vec![],
                        )
                    })?;

                let body_exec_result = self.run_in_local_env(|rt| {
                    let mut inside_results: Vec<StmtResult> = Vec::new();
                    for proof_stmt in stmt.proof.iter() {
                        let proof_exec_result = rt.exec_stmt(proof_stmt)?;
                        inside_results.push(proof_exec_result);
                    }

                    let target_result = rt.verify_fact_return_err_if_not_true(
                        &stmt.fact,
                        &VerifyState::new(0, false),
                    )?;
                    inside_results.push(target_result);

                    let claim_verification =
                        ClaimFactVerificationResult::new(stmt.fact.clone(), stmt.proof.len())
                            .into();

                    Ok(NonFactualStmtSuccess::new_with_claim_verification(
                        stmt.clone().into(),
                        InferResult::new(),
                        inside_results,
                        claim_verification,
                    )
                    .into())
                });

                let non_err_after_body: StmtResult = match body_exec_result {
                    Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
                    Err(runtime_error) => return Err(runtime_error),
                };
                let infer_result_after_store = self
                    .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                        stmt.fact.clone(),
                        InferReason::ProvedClaim,
                    )?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
        }
    }
}
