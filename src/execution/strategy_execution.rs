use crate::prelude::*;

impl Runtime {
    pub fn exec_def_strategy_stmt(
        &mut self,
        stmt: &DefStrategyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let strategy_name = stmt.name.clone();
        let well_definedness = self
            .verify_fact_well_defined_result(
                &Fact::ForallFact(stmt.forall_fact.clone()),
                &VerifyState::initial(),
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "strategy: forall fact is not well defined".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let body_exec_result: StmtResult = self.run_in_local_env(|rt| {
            let mut assumption_infers = rt
                .define_params_with_type(
                    &stmt.forall_fact.typed_parameters,
                    false,
                    BindingScope::LocalBinder,
                )
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;

            for dom_fact in stmt.forall_fact.dom_facts.iter() {
                let mut dom_infers = rt
                    .store_with_well_defined_verification_and_infer_with_default_verify_state(
                        dom_fact.clone(),
                    )?;
                dom_infers
                    .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
                assumption_infers.new_infer_result_inside(dom_infers);
            }

            let mut proof_steps = vec![];
            let proof_len = stmt.prove_process.len();
            for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                let result = rt.execute_statement(proof_stmt)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            format!("strategy `{}` failed: proof step is unknown", strategy_name),
                            proof_stmt.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::proof_step_unknown(
                                proof_stmt.clone(),
                                proof_index + 1,
                                proof_len,
                                &result,
                            ),
                        ),
                    )));
                }
                proof_steps.push(result);
            }

            let mut conclusion_checks = Vec::new();
            let then_count = stmt.forall_fact.then_facts.len();
            let then_verify_state = VerifyState::initial();
            for (then_index, then_fact) in stmt.forall_fact.then_facts.iter().enumerate() {
                let then_goal = then_fact.clone().to_fact();
                let result = rt.verify_fact_allow_unknown(&then_goal, &then_verify_state)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(then_goal.clone().into()),
                            format!(
                                "strategy `{}` failed: cannot prove then-clause",
                                strategy_name
                            ),
                            then_fact.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::then_clause_unknown_fact(
                                then_goal,
                                then_index + 1,
                                then_count,
                                result
                                    .as_fact_unknown()
                                    .expect("unknown fact verification carries an unknown result"),
                            ),
                        ),
                    )));
                }
                conclusion_checks.push(result);
            }

            // These assumptions and proof children belong to the strategy's
            // temporary forall scope. Freeze their exact identities before
            // `run_in_local_env` removes that Runtime environment.
            rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
            for result in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(result)?;
            }
            for result in conclusion_checks.iter_mut() {
                rt.attach_known_fact_ids_to_verify_fact_result(result)?;
            }

            Ok(
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefStrategyStmt(
                    Box::new(SuccessDefStrategyStmtResult {
                        statement: stmt.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                        verification: Some(SuccessVerifyStrategyDefinitionResult::new(
                            stmt.name.clone(),
                            stmt.forall_fact.clone(),
                            well_definedness,
                            SuccessVerifyLocalProofScopeResult::new(assumption_infers, Vec::new()),
                            proof_steps,
                            conclusion_checks,
                        )),
                    }),
                ))
                .into(),
            )
        })?;

        self.store_def_strategy(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let infer_result_after_store = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                Fact::ForallFact(stmt.forall_fact.clone()),
            )?;

        Ok(body_exec_result.with_infers(infer_result_after_store))
    }

    pub fn exec_def_strategy_stmt_affect_environment_only(
        &mut self,
        stmt: &DefStrategyStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.store_def_strategy(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::StatementWithVerification,
        )?;

        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefStrategyStmt(Box::new(
                SuccessDefStrategyStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            )))
            .into(),
        )
    }
}
