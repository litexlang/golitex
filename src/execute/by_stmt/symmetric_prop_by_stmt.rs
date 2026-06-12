use super::helpers_by_stmt::user_defined_prop_arity;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_symmetric_prop_stmt(
        &mut self,
        stmt: &BySymmetricPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let (prop_name, gather) = stmt.symmetric_prop_registration().map_err(|msg| {
            RuntimeError::from(VerifyRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(msg, stmt.line_file.clone()),
            ))
        })?;

        let forall_arity = stmt
            .forall_fact
            .params_def_with_type
            .collect_param_names()
            .len();
        match user_defined_prop_arity(self, &prop_name) {
            Some(arity) => {
                if arity != forall_arity {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by symmetric_prop: `{}` must have arity {} to match the forall",
                            prop_name, forall_arity
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
                        "by symmetric_prop: `{}` must be a user-defined prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let inside_results = self.run_in_local_env(|rt| {
            let verify_state = VerifyState::new(0, false);
            let assumption_infer_result =
                rt.forall_assume_params_and_dom_in_current_env(&stmt.forall_fact, &verify_state)?;
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
                    format!("by symmetric_prop: failed to prove `{}`", stmt.forall_fact),
                    None,
                    inside_results,
                ));
            }
            inside_results.push(result);
            Ok(inside_results)
        })?;

        self.top_level_env().store_symmetric_prop_permutation(
            prop_name.clone(),
            gather.clone(),
            stmt.line_file.clone(),
        )?;

        let mut infer_result = InferResult::new();
        infer_result.new_with_msg(format!(
            "registered symmetric permutation {:?} for `{}`",
            gather, prop_name
        ));
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }
}
