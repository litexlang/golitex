use crate::prelude::*;

impl Runtime {
    pub(crate) fn exec_checked_goal_block(
        &mut self,
        source_stmt: Stmt,
        fact: &Fact,
        proof: &[Stmt],
        label: &str,
    ) -> Result<StmtResult, RuntimeError> {
        let prechecked_well_definedness =
            self.verify_checked_goal_block_well_definedness(&source_stmt, fact, label)?;
        self.verify_checked_goal_block(
            source_stmt,
            fact,
            proof,
            label,
            &prechecked_well_definedness,
        )
    }

    fn verify_checked_goal_block_well_definedness(
        &mut self,
        source_stmt: &Stmt,
        fact: &Fact,
        label: &str,
    ) -> Result<Environment, RuntimeError> {
        if matches!(fact, Fact::ForallFactWithIff(_)) {
            unreachable!("checked goal block forall with iff is not supported");
        }

        let verify_result = match fact {
            Fact::ForallFact(forall_fact) => self
                .verify_forall_fact_well_defined_and_collect_certificate(
                    forall_fact,
                    &UseContextVerifyState::new(0, false),
                ),
            _ => self
                .verify_fact_well_defined(fact, &UseContextVerifyState::new(0, false))
                .map(|_| Environment::new_empty_env()),
        };
        verify_result.map_err(|error| {
            short_exec_error(
                source_stmt.clone(),
                format!("{label}: fact is not well defined"),
                Some(error),
                vec![],
            )
        })
    }

    fn verify_checked_goal_block(
        &mut self,
        source_stmt: Stmt,
        fact: &Fact,
        proof: &[Stmt],
        label: &str,
        prechecked_well_definedness: &Environment,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            Fact::ForallFactWithIff(_) => {
                unreachable!("checked goal block forall with iff is not supported")
            }
            Fact::ForallFact(forall_fact) => {
                let result: StmtResult = self.run_in_local_env(|rt| {
                    let captures_well_definedness = rt.captures_well_definedness();
                    if captures_well_definedness {
                        rt.begin_statement_well_definedness_capture();
                    }
                    let body_result: Result<(InferResult, Vec<StmtResult>), RuntimeError> =
                        (|| {
                            let mut assumption_infers = rt
                                .forall_assume_params_and_dom_in_current_env(
                                    forall_fact,
                                    &UseContextVerifyState::new(0, false),
                                )?;
                            let mut inside_results = Vec::new();
                            for (proof_index, proof_stmt) in proof.iter().enumerate() {
                                let result = rt.exec_stmt(proof_stmt)?;
                                if result.is_unknown() {
                                    return Err(UnknownRuntimeError(
                                        RuntimeErrorStruct::new_with_output(
                                            Some(proof_stmt.clone()),
                                            format!("{label} failed: proof step is unknown"),
                                            proof_stmt.line_file(),
                                            None,
                                            vec![],
                                            RuntimeErrorOutput::proof_step_unknown(
                                                proof_stmt.clone(),
                                                proof_index + 1,
                                                proof.len(),
                                                &result,
                                            ),
                                        ),
                                    )
                                    .into());
                                }
                                inside_results.push(result);
                            }

                            rt.install_prechecked_well_definedness_certificate(
                                prechecked_well_definedness,
                            )?;
                            let then_count = forall_fact.then_facts.len();
                            let then_verify_state = UseContextVerifyState::new(0, true);
                            for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate()
                            {
                                let mut result = rt.verify_exist_or_and_chain_atomic_fact(
                                    then_fact,
                                    &then_verify_state,
                                )?;
                                if result.is_unknown() {
                                    let then_goal = then_fact.clone().to_fact();
                                    result = rt.structured_unknown_result_for_failed_fact(
                                        &then_goal,
                                        &then_verify_state,
                                        result,
                                    )?;
                                    return Err(UnknownRuntimeError(
                                        RuntimeErrorStruct::new_with_output(
                                            Some(then_goal.clone().into()),
                                            format!("{label} failed: cannot prove then-clause"),
                                            then_fact.line_file(),
                                            None,
                                            vec![],
                                            RuntimeErrorOutput::then_clause_unknown(
                                                then_goal,
                                                then_index + 1,
                                                then_count,
                                                &result,
                                            ),
                                        ),
                                    )
                                    .into());
                                }
                                inside_results.push(result);
                            }

                            rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
                            for result in inside_results.iter_mut() {
                                rt.attach_known_fact_ids_to_stmt_result(result)?;
                            }
                            Ok((assumption_infers, inside_results))
                        })();

                    match body_result {
                        Ok((assumption_infers, inside_results)) => {
                            let well_definedness = if captures_well_definedness {
                                rt.end_statement_well_definedness_capture()?
                            } else {
                                WellDefinednessCertificate::default()
                            };
                            let verification = ClaimForallVerificationResult::new(
                                forall_fact.clone(),
                                assumption_infers.clone(),
                                proof.len(),
                            )
                            .into();
                            Ok(NonFactualStmtSuccess::new_with_claim_verification(
                                source_stmt.clone(),
                                InferResult::new(),
                                inside_results,
                                verification,
                            )
                            .with_local_proof_scope_verification(
                                LocalProofScopeVerificationResult::new(
                                    assumption_infers,
                                    Vec::new(),
                                    well_definedness,
                                ),
                            )
                            .into())
                        }
                        Err(error) => {
                            if captures_well_definedness {
                                rt.discard_statement_well_definedness_capture();
                            }
                            Err(error)
                        }
                    }
                })?;
                if result.is_unknown() {
                    return Err(UnknownRuntimeError(RuntimeErrorStruct::new(
                        Some(source_stmt),
                        format!("{label} failed: cannot prove `{fact}`"),
                        fact.line_file(),
                        None,
                        vec![],
                    ))
                    .into());
                }
                Ok(result)
            }
            _ => self.run_in_local_env(|rt| {
                let captures_well_definedness = rt.captures_well_definedness();
                if captures_well_definedness {
                    rt.begin_statement_well_definedness_capture();
                }
                let body_result: Result<Vec<StmtResult>, RuntimeError> = (|| {
                    let mut inside_results = Vec::new();
                    for proof_stmt in proof.iter() {
                        inside_results.push(rt.exec_stmt(proof_stmt)?);
                    }
                    inside_results.push(rt.verify_fact_return_err_if_not_true(
                        fact,
                        &UseContextVerifyState::new(0, true),
                    )?);
                    for result in inside_results.iter_mut() {
                        rt.attach_known_fact_ids_to_stmt_result(result)?;
                    }
                    Ok(inside_results)
                })();

                match body_result {
                    Ok(inside_results) => {
                        let well_definedness = if captures_well_definedness {
                            rt.end_statement_well_definedness_capture()?
                        } else {
                            WellDefinednessCertificate::default()
                        };
                        let verification =
                            ClaimFactVerificationResult::new(fact.clone(), proof.len()).into();
                        Ok(NonFactualStmtSuccess::new_with_claim_verification(
                            source_stmt.clone(),
                            InferResult::new(),
                            inside_results,
                            verification,
                        )
                        .with_local_proof_scope_verification(
                            LocalProofScopeVerificationResult::new(
                                InferResult::new(),
                                Vec::new(),
                                well_definedness,
                            ),
                        )
                        .into())
                    }
                    Err(error) => {
                        if captures_well_definedness {
                            rt.discard_statement_well_definedness_capture();
                        }
                        Err(error)
                    }
                }
            }),
        }
    }
}
