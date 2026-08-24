use crate::prelude::*;

impl Runtime {
    pub fn exec_example_stmt(&mut self, stmt: &ExampleStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_checked_goal_block(stmt.clone().into(), &stmt.fact, &stmt.proof, EXAMPLE)
    }

    pub fn exec_checked_goal_block(
        &mut self,
        source_stmt: Stmt,
        fact: &Fact,
        proof: &[Stmt],
        label: &str,
    ) -> Result<StmtResult, RuntimeError> {
        let (well_definedness, prechecked_well_definedness) =
            self.verify_checked_goal_block_well_definedness(&source_stmt, fact, label)?;
        self.verify_checked_goal_block(
            source_stmt,
            fact,
            proof,
            label,
            well_definedness,
            &prechecked_well_definedness,
        )
    }

    fn verify_checked_goal_block_well_definedness(
        &mut self,
        source_stmt: &Stmt,
        fact: &Fact,
        label: &str,
    ) -> Result<(SuccessVerifyFactWellDefinedResult, Environment), RuntimeError> {
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
                .verify_fact_well_defined_result(fact, &UseContextVerifyState::new(0, false))
                .map(|result| (result, Environment::new_empty_env())),
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
        well_definedness: SuccessVerifyFactWellDefinedResult,
        prechecked_well_definedness: &Environment,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            Fact::ForallFactWithIff(_) => {
                unreachable!("checked goal block forall with iff is not supported")
            }
            Fact::ForallFact(forall_fact) => {
                let result: StmtResult = self.run_in_local_env(|rt| {
                    let body_result: Result<(SuccessInferResult, Vec<StmtResult>), RuntimeError> =
                        (|| {
                            let mut assumption_infers = rt
                                .forall_assume_params_and_dom_in_current_env(
                                    forall_fact,
                                    &UseContextVerifyState::new(0, false),
                                )?;
                            let mut inside_results = Vec::new();
                            for (proof_index, proof_stmt) in proof.iter().enumerate() {
                                let result = rt.execute_statement(proof_stmt)?;
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
                        Ok((assumption_infers, mut inside_results)) => {
                            let conclusion_checks = inside_results.split_off(proof.len());
                            let proof_scope = SuccessVerifyLocalProofScopeResult::new(
                                assumption_infers,
                                Vec::new(),
                            );
                            let verification = SuccessVerifyClaimForallResult::new(
                                forall_fact.clone(),
                                well_definedness,
                                proof_scope,
                                inside_results,
                                conclusion_checks,
                            )
                            .into();
                            let common = SuccessStmtCommonResult::new(SuccessInferResult::new());
                            match source_stmt.clone() {
                                Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(statement)) => {
                                    Ok(SuccessProofBlockStmtResult::ClaimStmt(Box::new(
                                        SuccessClaimStmtResult {
                                            statement,
                                            common,
                                            verification: Some(verification),
                                        },
                                    ))
                                    .into())
                                }
                                Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(statement)) => {
                                    Ok(SuccessProofBlockStmtResult::ExampleStmt(Box::new(
                                        SuccessExampleStmtResult {
                                            statement,
                                            common,
                                            verification: Some(verification),
                                        },
                                    ))
                                    .into())
                                }
                                _ => unreachable!(
                                    "checked goal block source must be claim or example"
                                ),
                            }
                        }
                        Err(error) => Err(error),
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
                let body_result: Result<Vec<StmtResult>, RuntimeError> = (|| {
                    let mut inside_results = Vec::new();
                    for proof_stmt in proof.iter() {
                        inside_results.push(rt.execute_statement(proof_stmt)?);
                    }
                    inside_results
                        .push(rt.verify_fact_or_error(fact, &UseContextVerifyState::new(0, true))?);
                    for result in inside_results.iter_mut() {
                        rt.attach_known_fact_ids_to_stmt_result(result)?;
                    }
                    Ok(inside_results)
                })();

                match body_result {
                    Ok(mut inside_results) => {
                        let conclusion_check = inside_results.pop().ok_or_else(|| {
                            UnknownRuntimeError(RuntimeErrorStruct::new(
                                Some(source_stmt.clone()),
                                format!("{label} failed: missing goal check result"),
                                fact.line_file(),
                                None,
                                Vec::new(),
                            ))
                        })?;
                        let proof_scope = SuccessVerifyLocalProofScopeResult::new(
                            SuccessInferResult::new(),
                            Vec::new(),
                        );
                        let verification = SuccessVerifyClaimFactResult::new(
                            fact.clone(),
                            well_definedness,
                            proof_scope,
                            inside_results,
                            conclusion_check,
                        )
                        .into();
                        let common = SuccessStmtCommonResult::new(SuccessInferResult::new());
                        match source_stmt.clone() {
                            Stmt::ProofBlock(ProofBlockStmt::ClaimStmt(statement)) => {
                                Ok(SuccessProofBlockStmtResult::ClaimStmt(Box::new(
                                    SuccessClaimStmtResult {
                                        statement,
                                        common,
                                        verification: Some(verification),
                                    },
                                ))
                                .into())
                            }
                            Stmt::ProofBlock(ProofBlockStmt::ExampleStmt(statement)) => {
                                Ok(SuccessProofBlockStmtResult::ExampleStmt(Box::new(
                                    SuccessExampleStmtResult {
                                        statement,
                                        common,
                                        verification: Some(verification),
                                    },
                                ))
                                .into())
                            }
                            _ => unreachable!("checked goal block source must be claim or example"),
                        }
                    }
                    Err(error) => Err(error),
                }
            }),
        }
    }
}
