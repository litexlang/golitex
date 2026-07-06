use crate::prelude::*;

impl Runtime {
    pub fn exec_def_thm_stmt(&mut self, stmt: &DefThmStmt) -> Result<StmtResult, RuntimeError> {
        let thm_names = stmt.names.join(", ");
        let keyword = stmt.keyword();
        if stmt.is_axiom() && self.strict_mode {
            return Err(short_exec_error(
                stmt.clone().into(),
                DefThmStmt::strict_mode_rejection_message(),
                None,
                vec![],
            ));
        }

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
        })?;

        let body_exec_result: StmtResult = if stmt.is_axiom() {
            NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), vec![]).into()
        } else {
            self.run_in_local_env(|rt| {
                rt.define_params_with_type(
                    &stmt.forall_fact.params_def_with_type,
                    false,
                    ParamObjType::Forall,
                )
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;

                for dom_fact in stmt.forall_fact.dom_facts.iter() {
                    rt.verify_well_defined_and_store_and_infer(
                        dom_fact.clone(),
                        &VerifyState::new(0, false),
                    )?;
                }

                let mut inside_results = vec![];
                let proof_len = stmt.prove_process.len();
                for (proof_index, proof_stmt) in stmt.prove_process.iter().enumerate() {
                    let result = rt.exec_stmt(proof_stmt)?;
                    if result.is_unknown() {
                        return Err(RuntimeError::from(UnknownRuntimeError(
                            RuntimeErrorStruct::new_with_output(
                                Some(proof_stmt.clone()),
                                format!(
                                    "{} `{}` failed: proof step is unknown",
                                    keyword, thm_names
                                ),
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

                Ok(NonFactualStmtSuccess::new(
                    stmt.clone().into(),
                    InferResult::new(),
                    inside_results,
                )
                .into())
            })?
        };

        self.store_def_thm(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        let infer_result_after_store = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                Fact::ForallFact(stmt.forall_fact.clone()),
                InferReason::Other(stmt.store_reason().to_string()),
            )?;

        Ok(body_exec_result.with_infers(infer_result_after_store))
    }
}
