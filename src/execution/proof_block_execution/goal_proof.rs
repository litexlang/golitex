use crate::prelude::*;

impl Runtime {
    pub fn exec_example_stmt(&mut self, stmt: &ExampleStmt) -> Result<StmtResult, RuntimeError> {
        let verification =
            self.verify_checked_goal_block(stmt.clone().into(), &stmt.fact, &stmt.proof, EXAMPLE)?;
        Ok(
            SuccessProofBlockStmtResult::ExampleStmt(Box::new(SuccessExampleStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                verification: Some(verification),
            }))
            .into(),
        )
    }

    pub fn verify_checked_goal_block(
        &mut self,
        source_stmt: Stmt,
        fact: &Fact,
        proof: &[Stmt],
        label: &str,
    ) -> Result<SuccessCheckedGoalBlockResult, RuntimeError> {
        let (well_definedness, prechecked_well_definedness) =
            self.verify_checked_goal_block_well_definedness(&source_stmt, fact, label)?;
        self.verify_checked_goal_block_after_well_definedness(
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
    ) -> Result<
        (
            WellDefinedFactResult,
            WellDefinednessEnvironmentDelta,
        ),
        RuntimeError,
    > {
        if matches!(fact, Fact::ForallFactWithIff(_)) {
            unreachable!("checked goal block forall with iff is not supported");
        }

        let verify_result = match fact {
            Fact::ForallFact(forall_fact) => self
                .verify_forall_fact_well_defined_and_collect_certificate(
                    forall_fact,
                    &VerifyState::initial(),
                ),
            _ => self
                .verify_fact_well_defined_result(fact, &VerifyState::initial())
                .map(|result| (result, WellDefinednessEnvironmentDelta::new())),
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

    fn verify_checked_goal_block_after_well_definedness(
        &mut self,
        _source_stmt: Stmt,
        fact: &Fact,
        proof: &[Stmt],
        label: &str,
        well_definedness: WellDefinedFactResult,
        prechecked_well_definedness: &WellDefinednessEnvironmentDelta,
    ) -> Result<SuccessCheckedGoalBlockResult, RuntimeError> {
        match fact {
            Fact::ForallFactWithIff(_) => {
                unreachable!("checked goal block forall with iff is not supported")
            }
            Fact::ForallFact(forall_fact) => self.run_in_local_env(|rt| {
                let body_result: Result<
                    (SuccessInferResult, Vec<StmtResult>, Vec<VerifyFactResult>),
                    RuntimeError,
                > =
                    (|| {
                        let mut assumption_infers = rt
                            .forall_assume_params_and_dom_in_current_env(
                                forall_fact,
                                &VerifyState::initial(),
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
                        let then_verify_state = VerifyState::initial();
                        let mut conclusion_checks = Vec::new();
                        for (then_index, then_fact) in forall_fact.then_facts.iter().enumerate() {
                            let then_goal = then_fact.clone().to_fact();
                            let result =
                                rt.verify_fact_allow_unknown(&then_goal, &then_verify_state)?;
                            if result.is_unknown() {
                                return Err(UnknownRuntimeError(
                                    RuntimeErrorStruct::new_with_output(
                                        Some(then_goal.clone().into()),
                                        format!("{label} failed: cannot prove then-clause"),
                                        then_fact.line_file(),
                                        None,
                                        vec![],
                                        RuntimeErrorOutput::then_clause_unknown_fact(
                                            then_goal,
                                            then_index + 1,
                                            then_count,
                                            result.as_fact_unknown().expect(
                                                "unknown fact verification carries an unknown result",
                                            ),
                                        ),
                                    ),
                                )
                                .into());
                            }
                            conclusion_checks.push(result);
                        }

                        rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
                        for result in inside_results.iter_mut() {
                            rt.attach_known_fact_ids_to_stmt_result(result)?;
                        }
                        for result in conclusion_checks.iter_mut() {
                            rt.attach_known_fact_ids_to_verify_fact_result(result)?;
                        }
                        Ok((assumption_infers, inside_results, conclusion_checks))
                    })();

                match body_result {
                    Ok((assumption_infers, inside_results, conclusion_checks)) => {
                        let domain =
                            SuccessVerifyLocalProofScopeResult::new(assumption_infers, Vec::new());
                        Ok(SuccessCheckedGoalBlockResult::new(
                            forall_fact.clone().into(),
                            well_definedness,
                            domain,
                            inside_results,
                            conclusion_checks,
                        ))
                    }
                    Err(error) => Err(error),
                }
            }),
            _ => self.run_in_local_env(|rt| {
                let body_result: Result<(Vec<StmtResult>, VerifyFactResult), RuntimeError> = (|| {
                    let mut proof_steps = Vec::new();
                    for proof_stmt in proof.iter() {
                        proof_steps.push(rt.execute_statement(proof_stmt)?);
                    }
                    let mut conclusion_check =
                        rt.verify_fact_or_error(fact, &VerifyState::initial())?;
                    for result in proof_steps.iter_mut() {
                        rt.attach_known_fact_ids_to_stmt_result(result)?;
                    }
                    rt.attach_known_fact_ids_to_verify_fact_result(&mut conclusion_check)?;
                    Ok((proof_steps, conclusion_check))
                })();

                match body_result {
                    Ok((proof_steps, conclusion_check)) => {
                        let domain = SuccessVerifyLocalProofScopeResult::new(
                            SuccessInferResult::new(),
                            Vec::new(),
                        );
                        Ok(SuccessCheckedGoalBlockResult::new(
                            fact.clone(),
                            well_definedness,
                            domain,
                            proof_steps,
                            vec![conclusion_check],
                        ))
                    }
                    Err(error) => Err(error),
                }
            }),
        }
    }
}
