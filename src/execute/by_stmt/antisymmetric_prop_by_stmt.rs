use super::helpers_by_stmt::user_defined_prop_arity;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_antisymmetric_prop_stmt(
        &mut self,
        stmt: &ByAntisymmetricPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.antisymmetric_prop_name().map_err(|msg| {
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
                            "by antisymmetric_prop: `{}` must be a binary user-defined prop",
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
                        "by antisymmetric_prop: `{}` must be a user-defined prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let well_definedness = self.verify_fact_well_defined_result(
            &Fact::ForallFact(stmt.forall_fact.clone()),
            &UseContextVerifyState::new(0, false),
        )?;

        let (proof_steps, forall_check, assumption_infer_result) = self.run_in_local_env(|rt| {
            let verify_state = UseContextVerifyState::new(0, false);
            let assumption_infer_result =
                rt.forall_assume_params_and_dom_in_current_env(&stmt.forall_fact, &verify_state)?;
            let verification_assumption_infer_result = assumption_infer_result.clone();
            let mut infer_result = SuccessInferResult::new();
            let mut proof_steps: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                proof_steps.push(rt.exec_stmt(proof_stmt)?);
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
                    format!(
                        "by antisymmetric_prop: failed to prove `{}`",
                        stmt.forall_fact
                    ),
                    None,
                    proof_steps,
                ));
            }
            let mut verification_assumption_infer_result = verification_assumption_infer_result;
            rt.attach_known_fact_ids_to_infer_result(&mut verification_assumption_infer_result)?;
            for proof_step in proof_steps.iter_mut() {
                rt.attach_known_fact_ids_to_stmt_result(proof_step)?;
            }
            rt.attach_known_fact_ids_to_stmt_result(&mut result)?;
            Ok((proof_steps, result, verification_assumption_infer_result))
        })?;

        self.top_level_env()
            .store_antisymmetric_prop_name(prop_name.clone());

        let mut infer_result = SuccessInferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as antisymmetric", prop_name));
        let by_verification = SuccessVerifyByPropRegistrationResult::new(
            "antisymmetric".to_string(),
            prop_name,
            stmt.forall_fact.clone(),
            well_definedness,
            assumption_infer_result,
            proof_steps,
            forall_check,
        );
        Ok(SuccessByStmtResult::ByAntisymmetricPropStmt(Box::new(
            SuccessByAntisymmetricPropStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(by_verification),
            },
        ))
        .into())
    }

    pub fn exec_by_antisymmetric_prop_stmt_affect_environment_only(
        &mut self,
        stmt: &ByAntisymmetricPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let prop_name = stmt.antisymmetric_prop_name().map_err(|msg| {
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
                            "by antisymmetric_prop: `{}` must be a binary user-defined prop",
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
                        "by antisymmetric_prop: `{}` must be a user-defined prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        self.top_level_env()
            .store_antisymmetric_prop_name(prop_name.clone());
        let mut infer_result = SuccessInferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as antisymmetric", prop_name));
        Ok(SuccessByStmtResult::ByAntisymmetricPropStmt(Box::new(
            SuccessByAntisymmetricPropStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            },
        ))
        .into())
    }
}
