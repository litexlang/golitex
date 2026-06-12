use crate::prelude::*;

impl Runtime {
    pub fn exec_by_thm_stmt(&mut self, stmt: &ByThmStmt) -> Result<StmtResult, RuntimeError> {
        let thm_name = stmt.name.to_string();
        let thm = self.get_thm_definition_by_name(&thm_name).ok_or_else(|| {
            short_exec_error(
                stmt.clone().into(),
                format!("by thm: theorem `{}` is not defined", stmt.name),
                None,
                vec![],
            )
        })?;

        let verify_state = VerifyState::new(0, false);
        let arg_type_result = self
            .verify_args_satisfy_param_def_flat_types(
                &thm.forall_fact.params_def_with_type,
                &stmt.args,
                &verify_state,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: arguments do not match theorem parameters",
                        stmt.name
                    ),
                    Some(e),
                    vec![],
                )
            })?;
        if arg_type_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "by thm `{}`: could not verify argument parameter types",
                    stmt.name
                ),
                None,
                vec![arg_type_result],
            ));
        }

        let param_to_arg_map = thm
            .forall_fact
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&stmt.args);

        let mut infer_result = InferResult::new();
        Self::merge_stmt_result_infers(&mut infer_result, &arg_type_result);
        let mut inside_results = vec![arg_type_result];
        let mut domain_facts = Vec::new();
        for dom_fact in thm.forall_fact.dom_facts.iter() {
            let instantiated_dom = self
                .inst_fact(
                    dom_fact,
                    &param_to_arg_map,
                    ParamObjType::Forall,
                    Some(stmt.line_file.clone()),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to instantiate domain fact `{}`",
                            stmt.name, dom_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            let dom_result = self
                .verify_fact_full(&instantiated_dom, &verify_state)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to verify domain fact `{}`",
                            stmt.name, instantiated_dom
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            if dom_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by thm `{}`: domain fact `{}` is not verified",
                        stmt.name, instantiated_dom
                    ),
                    None,
                    vec![dom_result],
                ));
            }
            Self::merge_stmt_result_infers(&mut infer_result, &dom_result);
            domain_facts.push(instantiated_dom.to_string());
            inside_results.push(dom_result);
        }

        let mut stored_then_facts = Vec::new();
        for then_fact in thm.forall_fact.then_facts.iter() {
            let instantiated_then = self
                .inst_exist_or_and_chain_atomic_fact(
                    then_fact,
                    &param_to_arg_map,
                    ParamObjType::Forall,
                    Some(&stmt.line_file),
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to instantiate then fact `{}`",
                            stmt.name, then_fact
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            stored_then_facts.push(instantiated_then.to_string());
            infer_result.new_infer_result_inside(
                self.verify_exist_or_and_chain_atomic_fact_well_defined_and_store_and_infer_with_reason(
                    &instantiated_then,
                    &verify_state,
                    InferReason::TheoremInstantiation,
                )
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by thm `{}`: failed to store instantiated then fact `{}`",
                            stmt.name, instantiated_then
                        ),
                        Some(e),
                        vec![],
                    )
                })?,
            );
        }

        let by_verification = ByTheoremVerificationResult::new(
            thm_name,
            stmt.args.iter().map(|arg| arg.to_string()).collect(),
            domain_facts,
            stored_then_facts,
        );
        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result,
            inside_results,
            by_verification.into(),
        )
        .into())
    }

    fn merge_stmt_result_infers(infer_result: &mut InferResult, stmt_result: &StmtResult) {
        infer_result.new_infer_result_inside(stmt_result.infer_result());
    }
}
