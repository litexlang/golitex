use super::support::user_defined_prop_arity;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_transitive_prop_stmt(
        &mut self,
        stmt: &ByTransitivePropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.transitive_prop_name().map_err(|msg| {
            RuntimeError::from(VerifyRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, stmt.line_file.clone()),
            ))
        })?;

        match user_defined_prop_arity(self, &prop_name) {
            Some(arity) => {
                if arity != 2 {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by transitive_prop: `{}` must be a binary user-defined prop",
                            prop_name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
            None => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by transitive_prop: `{}` must be a user-defined prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let well_definedness = self.verify_fact_well_defined_result(
            &Fact::ForallFact(stmt.forall_fact.clone()),
            &VerifyState::initial(),
        )?;

        let (proof_steps, forall_check) = self.run_in_local_env(|rt| {
            let verify_state = VerifyState::initial();
            let assumption_infer_result =
                rt.forall_assume_params_and_dom_in_current_env(&stmt.forall_fact, &verify_state)?;
            let mut infer_result = SuccessInferResult::new();
            let mut proof_steps: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                proof_steps.push(rt.execute_statement(proof_stmt)?);
            }
            let mut result = rt.forall_verify_then_facts_in_current_env(
                &stmt.forall_fact,
                &verify_state,
                &mut infer_result,
                assumption_infer_result,
                None,
            )?;
            if result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by transitive_prop: failed to prove `{}`", stmt.forall_fact),
                    None,
                    proof_steps,
                ));
            }
            for proof_step in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(proof_step)?;
            }
            rt.attach_known_fact_ids_to_prove_fact_result(&mut result)?;
            Ok((proof_steps, result))
        })?;

        self.top_level_env()
            .store_transitive_prop_name(prop_name.clone());

        let mut infer_result = SuccessInferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as transitive", prop_name));
        let forall_check = Runtime::finish_fact_verification(well_definedness, forall_check);
        let by_verification = SuccessVerifyByPropRegistrationResult::new(
            "transitive".to_string(),
            prop_name,
            stmt.forall_fact.clone(),
            proof_steps,
            forall_check,
        );
        Ok(
            SuccessByStmtResult::ByTransitivePropStmt(Box::new(
                SuccessByTransitivePropStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(by_verification),
                },
            ))
            .into(),
        )
    }

    pub fn exec_by_transitive_prop_stmt_affect_environment_only(
        &mut self,
        stmt: &ByTransitivePropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.transitive_prop_name().map_err(|msg| {
            RuntimeError::from(VerifyRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, stmt.line_file.clone()),
            ))
        })?;

        match user_defined_prop_arity(self, &prop_name) {
            Some(arity) => {
                if arity != 2 {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by transitive_prop: `{}` must be a binary user-defined prop",
                            prop_name
                        ),
                        None,
                        vec![],
                    ));
                }
            }
            None => {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by transitive_prop: `{}` must be a user-defined prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        self.top_level_env()
            .store_transitive_prop_name(prop_name.clone());
        let mut infer_result = SuccessInferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as transitive", prop_name));
        Ok(
            SuccessByStmtResult::ByTransitivePropStmt(Box::new(
                SuccessByTransitivePropStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }
}
