use crate::prelude::*;

impl Runtime {
    pub fn exec_def_thm_stmt(&mut self, stmt: &DefThmStmt) -> Result<StmtResult, RuntimeError> {
        let thm_names = stmt.names.join(", ");
        self.verify_fact_well_defined(
            &Fact::ForallFact(stmt.forall_fact.clone()),
            &VerifyState::new(0, false),
        )
        .map_err(|e| {
            short_exec_error(
                stmt.clone().into(),
                "thm: forall fact is not well defined".to_string(),
                Some(e),
                vec![],
            )
        })?;

        let body_exec_result: StmtResult = self.run_in_local_env(|rt| {
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
                match result {
                    StmtResult::StmtUnknown(unknown) => {
                        return Err(RuntimeError::from(UnknownRuntimeError(
                            RuntimeErrorStruct::new_with_output(
                                Some(proof_stmt.clone()),
                                format!("thm `{}` failed: proof step is unknown", thm_names),
                                proof_stmt.line_file(),
                                None,
                                vec![],
                                RuntimeErrorOutput::proof_step_unknown(
                                    proof_stmt.clone(),
                                    proof_index + 1,
                                    proof_len,
                                    &unknown,
                                ),
                            ),
                        )));
                    }
                    _ => inside_results.push(result),
                }
            }

            let then_count = stmt.forall_fact.then_facts.len();
            for (then_index, then_fact) in stmt.forall_fact.then_facts.iter().enumerate() {
                let result = rt.verify_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &VerifyState::new(0, false),
                )?;
                match result {
                    StmtResult::StmtUnknown(unknown) => {
                        return Err(RuntimeError::from(UnknownRuntimeError(
                            RuntimeErrorStruct::new_with_output(
                                Some(then_fact.clone().to_fact().into()),
                                format!("thm `{}` failed: cannot prove then-clause", thm_names),
                                then_fact.line_file(),
                                None,
                                vec![],
                                RuntimeErrorOutput::then_clause_unknown(
                                    then_fact.clone().to_fact(),
                                    then_index + 1,
                                    then_count,
                                    &unknown,
                                ),
                            ),
                        )));
                    }
                    _ => inside_results.push(result),
                }
            }

            Ok(NonFactualStmtSuccess::new_with_accepted_by(
                stmt.clone().into(),
                InferResult::new(),
                inside_results,
                AcceptedByResult::proof_block(
                    Some(Fact::ForallFact(stmt.forall_fact.clone())),
                    proof_len + then_count,
                ),
            )
            .into())
        })?;

        self.store_def_thm(stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;

        Ok(body_exec_result)
    }
}
