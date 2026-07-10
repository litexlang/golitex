use crate::prelude::*;

impl Runtime {
    pub fn exec_def_thm_stmt(&mut self, stmt: &DefThmStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_def_thm_stmt_verify_well_definedness(stmt)?;
        let (body_exec_result, trust_summary) = self.exec_def_thm_stmt_verify_process(stmt)?;
        let infer_result_after_store =
            self.exec_def_thm_stmt_affect_environment(stmt, &trust_summary)?;

        Ok(body_exec_result.with_infers(infer_result_after_store))
    }

    fn exec_def_thm_stmt_verify_well_definedness(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<(), RuntimeError> {
        if stmt.is_axiom() && self.strict_mode {
            return Err(short_exec_error(
                stmt.clone().into(),
                DefThmStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }

        let keyword = stmt.keyword();
        self.verify_fact_well_defined(
            &Fact::ForallFact(stmt.forall_fact.clone()),
            &VerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                format!("{}: forall fact is not well defined", keyword),
                Some(e),
                vec![],
            )
        })
    }

    fn exec_def_thm_stmt_verify_process(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<(StmtResult, ProofTrustSummary), RuntimeError> {
        if stmt.is_axiom() {
            let trust_summary = ProofTrustSummary::from_dependency(
                "axiom",
                stmt.names.first().cloned(),
                stmt.line_file.clone(),
            );
            return Ok((
                NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), vec![]).into(),
                trust_summary,
            ));
        }

        let thm_names = stmt.names.join(", ");
        let keyword = stmt.keyword();
        self.run_in_local_env(|rt| {
            let mut assumption_infers = rt
                .define_params_with_type(
                    &stmt.forall_fact.params_def_with_type,
                    false,
                    ParamObjType::Forall,
                )
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;

            for dom_fact in stmt.forall_fact.dom_facts.iter() {
                let mut dom_infers = rt.verify_well_defined_and_store_and_infer(
                    dom_fact.clone(),
                    &VerifyState::new(0, false),
                )?;
                dom_infers
                    .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
                assumption_infers.new_infer_result_inside(dom_infers);
            }

            let mut inside_results = vec![];
            let proof_len = stmt.prove_process.len();
            for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                let result = rt.exec_stmt(proof_stmt)?;
                if result.is_unknown() {
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            format!("{} `{}` failed: proof step is unknown", keyword, thm_names),
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
            for (then_index, then_fact) in stmt.forall_fact.then_facts.iter().enumerate() {
                let mut result = rt.verify_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &VerifyState::new(0, false),
                )?;
                if result.is_unknown() {
                    let then_goal = then_fact.clone().to_fact();
                    result = result.wrap_unknown_for_fact(then_goal.clone());
                    return Err(RuntimeError::from(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_output(
                            Some(then_goal.clone().into()),
                            format!(
                                "{} `{}` failed: cannot prove then-clause",
                                keyword, thm_names
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

            let trust_summary = rt.proof_trust_summary_from_stmt_results(&inside_results);
            let theorem_verification = TheoremVerificationResult::new(
                stmt.names.clone(),
                stmt.forall_fact.clone(),
                assumption_infers,
                proof_len,
            );

            Ok((
                NonFactualStmtSuccess::new_with_theorem_verification(
                    stmt.clone().into(),
                    InferResult::new(),
                    inside_results,
                    theorem_verification,
                )
                .into(),
                trust_summary,
            ))
        })
    }

    pub(crate) fn exec_def_thm_stmt_affect_environment(
        &mut self,
        stmt: &DefThmStmt,
        trust_summary: &ProofTrustSummary,
    ) -> Result<InferResult, RuntimeError> {
        self.store_def_thm_with_trust(stmt, trust_summary)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        if self.only_exec_affect_environment {
            return self.store_trusted_fact_and_infer_with_reason_and_trust(
                Fact::ForallFact(stmt.forall_fact.clone()),
                InferReason::Other(stmt.store_reason_with_trust(trust_summary)),
                trust_summary.clone(),
            );
        }

        self.verify_well_defined_and_store_and_infer_with_reason_and_trust(
            Fact::ForallFact(stmt.forall_fact.clone()),
            &VerifyState::new(0, false),
            InferReason::Other(stmt.store_reason_with_trust(trust_summary)),
            trust_summary.clone(),
        )
    }

    pub(crate) fn exec_def_thm_stmt_affect_environment_only(
        &mut self,
        stmt: &DefThmStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let trust_summary = if stmt.is_axiom() {
            ProofTrustSummary::from_dependency(
                "axiom",
                stmt.names.first().cloned(),
                stmt.line_file.clone(),
            )
        } else {
            ProofTrustSummary::new()
        };
        let infer_result = self.exec_def_thm_stmt_affect_environment(stmt, &trust_summary)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}
