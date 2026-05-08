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

        let prop_definition = self.get_abstract_prop_definition_by_name(&prop_name);
        match prop_definition {
            Some(definition) => {
                if definition.params.len() != 2 {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by transitive_prop: `{}` must be a binary abstract_prop",
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
                        "by transitive_prop: `{}` must be an abstract_prop",
                        prop_name
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let inside_results = self.run_in_local_env(|rt| {
            let verify_state = VerifyState::new(0, false);
            let mut infer_result =
                rt.forall_assume_params_and_dom_in_current_env(&stmt.forall_fact, &verify_state)?;
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                inside_results.push(rt.exec_stmt(proof_stmt)?);
            }
            let result = rt.forall_verify_then_facts_in_current_env(
                &stmt.forall_fact,
                &verify_state,
                &mut infer_result,
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
            Ok(inside_results)
        })?;

        self.top_level_env()
            .store_transitive_prop_name(prop_name.clone());

        let mut infer_result = InferResult::new();
        infer_result.new_with_msg(format!("registered `{}` as transitive", prop_name));
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results).into())
    }
}
