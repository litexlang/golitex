use super::helpers_by_stmt::user_defined_prop_arity;
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

        let (inside_results, assumption_infer_result) = self.run_in_local_env(|rt| {
            let verify_state = VerifyState::new(0, false);
            let assumption_infer_result =
                rt.forall_assume_params_and_dom_in_current_env(&stmt.forall_fact, &verify_state)?;
            let verification_assumption_infer_result = assumption_infer_result.clone();
            let mut infer_result = InferResult::new();
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                inside_results.push(rt.exec_stmt(proof_stmt)?);
            }
            let result = rt.forall_verify_then_facts_in_current_env(
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
                    inside_results,
                ));
            }
            inside_results.push(result);
            Ok((inside_results, verification_assumption_infer_result))
        })?;

        self.top_level_env()
            .store_transitive_prop_name(prop_name.clone());

        let mut infer_result = InferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as transitive", prop_name));
        let by_verification = ByPropRegistrationVerificationResult::new(
            "transitive".to_string(),
            prop_name,
            stmt.forall_fact.clone(),
            assumption_infer_result,
            stmt.proof.len(),
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            by_verification.into(),
        )
        .into())
    }
}
