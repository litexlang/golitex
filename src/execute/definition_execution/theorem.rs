use crate::prelude::*;

impl Runtime {
    pub fn exec_def_thm_stmt(&mut self, stmt: &DefThmStmt) -> Result<StmtResult, RuntimeError> {
        let (well_definedness, execution_support) =
            self.exec_def_thm_stmt_verify_well_definedness(stmt)?;
        let body_exec_result =
            self.exec_def_thm_stmt_verify_process(stmt, well_definedness, &execution_support)?;
        let infer_result_after_store = self.exec_def_thm_stmt_affect_environment(stmt)?;

        Ok(body_exec_result.with_infers(infer_result_after_store))
    }

    /// Mathematical contract: a theorem statement is meaningful when its
    /// complete universal fact is well-defined.
    fn exec_def_thm_stmt_verify_well_definedness(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<
        (
            SuccessVerifyFactWellDefinedResult,
            WellDefinednessEnvironmentDelta,
        ),
        RuntimeError,
    > {
        self.verify_forall_fact_well_defined_and_collect_certificate(
            &stmt.forall_fact,
            &ProofSearchState::initial(),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                "thm: forall fact is not well defined".to_string(),
                Some(e),
                vec![],
            )
        })
    }

    fn exec_def_thm_stmt_verify_process(
        &mut self,
        stmt: &DefThmStmt,
        well_definedness: SuccessVerifyFactWellDefinedResult,
        prechecked_well_definedness: &WellDefinednessEnvironmentDelta,
    ) -> Result<StmtResult, RuntimeError> {
        let thm_name = stmt.name.clone();
        let keyword = THM;
        self.run_in_local_env(|rt| {
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
                let mut dom_infers = rt.store_with_well_defined_verification_and_infer(
                    dom_fact.clone(),
                    &ProofSearchState::initial(),
                )?;
                dom_infers
                    .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
                assumption_infers.new_infer_result_inside(dom_infers);
            }

            // Conclusion well-definedness may materialize template objects or
            // other checked definitions needed by an explicit proof step.
            // Install those exact prechecked effects after recreating the
            // theorem assumptions, before executing the proof body.
            rt.install_prechecked_well_definedness_certificate(prechecked_well_definedness)?;

            let mut inside_results = vec![];
            let proof_len = stmt.prove_process.len();
            for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                let result = rt.execute_statement(proof_stmt)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            format!("{} `{}` failed: proof step is unknown", keyword, thm_name),
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
                inside_results.push(result);
            }

            let then_count = stmt.forall_fact.then_facts.len();
            let then_verify_state = ProofSearchState::after_well_definedness();
            for (then_index, then_fact) in stmt.forall_fact.then_facts.iter().enumerate() {
                let mut result =
                    rt.verify_exist_or_and_chain_atomic_fact(then_fact, &then_verify_state)?;
                if result.is_unknown() {
                    let then_goal = then_fact.clone().to_fact();
                    result = rt.structured_unknown_result_for_failed_fact(
                        &then_goal,
                        &then_verify_state,
                        result,
                    )?;
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(then_goal.clone().into()),
                            format!(
                                "{} `{}` failed: cannot prove then-clause",
                                keyword, thm_name
                            ),
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
                    )));
                }
                inside_results.push(result);
            }

            // These premises live only in the theorem's temporary scope. Freeze
            // their identities before that scope is popped so compiler IR can
            // replay exact citations rather than recover them by proposition.
            rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
            for result in inside_results.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(result)?;
            }

            let conclusion_checks = inside_results.split_off(proof_len);
            let theorem_verification = SuccessVerifyTheoremResult::new(
                stmt.name.clone(),
                stmt.forall_fact.clone(),
                well_definedness,
                SuccessVerifyLocalProofScopeResult::new(assumption_infers, Vec::new()),
                inside_results,
                conclusion_checks,
            );

            Ok(
                SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(Box::new(
                    SuccessDefThmStmtResult {
                        statement: stmt.clone(),
                        common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                        verification: Some(theorem_verification),
                    },
                )))
                .into(),
            )
        })
    }

    pub fn exec_def_thm_stmt_affect_environment(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_def_thm(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        if self.current_execution_is_trusted_file() {
            return self.store_trusted_fact_and_infer_with_reason(
                Fact::ForallFact(stmt.forall_fact.clone()),
                InferReason::Other(stmt.store_reason().to_string()),
            );
        }

        self.store_without_well_defined_verification_and_infer_with_reason(
            Fact::ForallFact(stmt.forall_fact.clone()),
            InferReason::Other(stmt.store_reason().to_string()),
        )
    }

    pub fn exec_def_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_def_thm_stmt_affect_environment(stmt)?;
        Ok(
            SuccessStmtResult::Definition(SuccessDefinitionStmtResult::DefThmStmt(Box::new(
                SuccessDefThmStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            )))
            .into(),
        )
    }
}
