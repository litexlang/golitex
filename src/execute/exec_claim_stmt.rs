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
                    rt.define_params_with_type(
                        &forall_fact.params_def_with_type,
                        false,
                        ParamObjType::Forall,
                    )
                        .map_err(|define_params_error| {
                            exec_stmt_error_with_stmt_and_cause(
                                stmt.clone().into(),
                                define_params_error,
                            )
                        })?;

                    for dom_fact in forall_fact.dom_facts.iter() {
                        rt.verify_well_defined_and_store_and_infer(
                            dom_fact.clone(),
                            &VerifyState::new(0, false),
                        )?;
                    }

                    let mut inside_results = vec![];
                    let proof_len = stmt.proof.len();
                    for (proof_index, proof_stmt) in stmt.proof.iter().enumerate() {
                        let result = rt.exec_stmt(proof_stmt)?;
                        if result.is_unknown() {
                            return Err(
                                UnknownRuntimeError(RuntimeErrorStruct::new(
                                    Some(proof_stmt.clone()),
                                    format!(
                                        "claim failed: proof step {}/{} is unknown: `{}`\n{}",
                                        proof_index + 1,
                                        proof_len,
                                        proof_stmt,
                                        result.body_string()
                                    ),
                                    proof_stmt.line_file(),
                                    None,
                                    vec![],
                                ))
                                .into(),
                            );
                        }
                        inside_results.push(result);
                    }

                    let then_count = forall_fact.then_facts.len();
                    for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
                        let result = rt.verify_exist_or_and_chain_atomic_fact(
                            then_fact,
                            &VerifyState::new(0, false),
                        )?;
                        if result.is_unknown() {
                            return Err(
                                UnknownRuntimeError(RuntimeErrorStruct::new(
                                    Some(then_fact.clone().to_fact().into()),
                                    format!(
                                        "claim failed: cannot prove goal `{}`; then-clause {}/{} `{}` is unknown\n{}",
                                        stmt.fact,
                                        then_index + 1,
                                        then_count,
                                        then_fact,
                                        result.body_string()
                                    ),
                                    then_fact.line_file(),
                                    None,
                                    vec![],
                                ))
                                .into(),
                            );
                        }

                        inside_results.push(result);
                    }

                    Ok(NonFactualStmtSuccess::new(
                            stmt.clone().into(),
                            InferResult::new(),
                            inside_results,
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
                        format!(
                            "claim failed: cannot prove `{}`\n{}",
                            stmt.fact,
                            non_err_after_body.body_string()
                        ),
                        stmt.line_file.clone(),
                        None,
                        vec![],
                    ))
                    .into());
                }

                let infer_result_after_store = self
                    .verify_well_defined_and_store_and_infer_with_default_verify_state(
                        stmt.fact.clone(),
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

                    rt.verify_fact_return_err_if_not_true(&stmt.fact, &VerifyState::new(0, false))?;

                    Ok(NonFactualStmtSuccess::new(
                        stmt.clone().into(),
                        InferResult::new(),
                        inside_results,
                    )
                    .into())
                });

                let non_err_after_body: StmtResult = match body_exec_result {
                    Ok(non_err_stmt_exec_result) => non_err_stmt_exec_result,
                    Err(runtime_error) => return Err(runtime_error),
                };
                let infer_result_after_store = self
                    .verify_well_defined_and_store_and_infer_with_default_verify_state(
                        stmt.fact.clone(),
                    )?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
        }
    }
}
