use crate::prelude::*;

impl Runtime {
    pub fn exec_claim_stmt(&mut self, stmt: &ClaimStmt) -> Result<StmtResult, RuntimeError> {
        match &stmt.fact {
            Fact::ForallFactWithIff(_) => unreachable!("claim forall with iff is not supported"),
            Fact::ForallFact(forall_fact) => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        RuntimeError::ExecStmtError({
                            let __stmt: Stmt = stmt.clone().into();
                            let __message = "claim: fact is not well defined".to_string();
                            let __cause = Some(e);
                            let __inside = vec![];
                            let __line_file = __stmt.line_file();
                            let __previous_error = if __message.is_empty() {
                                __cause
                            } else {
                                Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                            };
                            RuntimeErrorStruct::new(
                                Some(__stmt),
                                __message,
                                __line_file,
                                __previous_error,
                                __inside,
                            )
                        })
                    })?;

                let body_exec_result = self.run_in_local_env(|rt| {
                    rt.define_params_with_type(&forall_fact.params_def_with_type, false)
                        .map_err(|define_params_error| {
                            RuntimeError::ExecStmtError({
            let __stmt: Stmt = stmt.clone().into();
            let __line_file = __stmt.line_file();
            RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(define_params_error), vec![])
        })
                        })?;

                    for dom_fact in forall_fact.dom_facts.iter() {
                        rt.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                            dom_fact.clone(),
                        )?;
                    }

                    let mut inside_results = vec![];
                    for proof_stmt in stmt.proof.iter() {
                        let result = rt.exec_stmt(proof_stmt)?;
                        inside_results.push(result);
                    }

                    for then_fact in forall_fact.then_facts.iter() {
                        let result = rt.verify_exist_or_and_chain_atomic_fact(
                            then_fact,
                            &VerifyState::new(0, false),
                        )?;
                        if result.is_unknown() {
                            return Err(
                                UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(stmt.fact.clone().into_stmt()),
                format!("claim failed: cannot prove `{}`", stmt.fact),
                stmt.line_file.clone(),
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
                Some(stmt.fact.clone().into_stmt()),
                format!("claim failed: cannot prove `{}`", stmt.fact),
                stmt.line_file.clone(),
                None,
                vec![],
            ))
            .into());
                }

                let infer_result_after_store =
                    self.store_fact_without_well_defined_verified_and_infer(stmt.fact.clone())?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
            _ => {
                self.verify_fact_well_defined(&stmt.fact, &VerifyState::new(0, false))
                    .map_err(|e| {
                        RuntimeError::ExecStmtError({
                            let __stmt: Stmt = stmt.clone().into();
                            let __message = "claim: fact is not well defined".to_string();
                            let __cause = Some(e);
                            let __inside = vec![];
                            let __line_file = __stmt.line_file();
                            let __previous_error = if __message.is_empty() {
                                __cause
                            } else {
                                Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                            };
                            RuntimeErrorStruct::new(
                                Some(__stmt),
                                __message,
                                __line_file,
                                __previous_error,
                                __inside,
                            )
                        })
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
                let infer_result_after_store =
                    self.store_fact_without_well_defined_verified_and_infer(stmt.fact.clone())?;

                Ok(non_err_after_body.with_infers(infer_result_after_store))
            }
        }
    }
}
