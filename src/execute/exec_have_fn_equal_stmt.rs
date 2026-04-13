use crate::prelude::*;

use super::exec_have_fn_equal_shared::{
    build_function_obj_with_param_names, param_defs_with_type_from_have_fn_clause,
};

impl Runtime {
    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeErrorStruct> {
        let fn_set_stored = self
            .add_mangled_prefix_to_fn_set_clause(
                &have_fn_equal_stmt.fn_set_clause,
                have_fn_equal_stmt.line_file.clone(),
            )
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: build fn set for storage failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        self.have_fn_equal_stmt_verify_well_defined(have_fn_equal_stmt, &fn_set_stored)
            .map_err(|e| {
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: verify well-defined failed".to_string(),
                    Some(RuntimeError::ExecStmtError(e)),
                    vec![],
                )
            })?;

        self.store_identifier_obj(&have_fn_equal_stmt.name)?;

        let function_identifier_obj = have_fn_equal_stmt.name.clone().into();
        let function_set_obj = fn_set_stored.clone().into();
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let mut infer_result = self
            .store_fact_without_well_defined_verified_and_infer(function_in_function_set_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(RuntimeError::ExecStmtError(store_fact_error)),
                    vec![],
                )
            })?;

        let param_defs_with_type =
            param_defs_with_type_from_have_fn_clause(&have_fn_equal_stmt.fn_set_clause);
        let param_names = ParamGroupWithSet::collect_param_names(
            &have_fn_equal_stmt.fn_set_clause.params_def_with_set,
        );
        let function_obj = build_function_obj_with_param_names(&have_fn_equal_stmt.name, &param_names);

        let function_equals_equal_to_fact: AtomicFact = EqualFact::new(
            function_obj,
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let mut forall_dom_facts: Vec<ExistOrAndChainAtomicFact> =
            Vec::with_capacity(have_fn_equal_stmt.fn_set_clause.dom_facts.len());
        for dom_fact in have_fn_equal_stmt.fn_set_clause.dom_facts.iter() {
            forall_dom_facts.push(dom_fact.clone().into());
        }
        let forall_fact = ForallFact::new(
            param_defs_with_type,
            forall_dom_facts,
            vec![function_equals_equal_to_fact.into()],
            have_fn_equal_stmt.line_file.clone(),
        );
        let forall_as_fact: Fact = forall_fact.into();
        let forall_infer_result = self
            .store_fact_without_well_defined_verified_and_infer(forall_as_fact)
            .map_err(|store_fact_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(RuntimeError::ExecStmtError(store_fact_error)),
                    vec![],
                )
            })?;

        infer_result.new_infer_result_inside(forall_infer_result);

        Ok((NonFactualStmtSuccess::new(
            have_fn_equal_stmt.clone().into(),
            infer_result,
            vec![],
        ))
        .into())
    }

    fn have_fn_equal_stmt_verify_well_defined(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeErrorStruct> {
        self.run_in_local_env(|rt| {
            rt.have_fn_equal_stmt_verify_well_defined_body(have_fn_equal_stmt, fn_set_stored)
        })
    }

    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeErrorStruct> {
        let verify_state = VerifyState::new(0, false);

        let function_set_obj = fn_set_stored.clone().into();
        self.verify_obj_well_defined_and_store_cache(&function_set_obj, &verify_state)
            .map_err(|well_defined_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        for param_def_with_set in have_fn_equal_stmt.fn_set_clause.params_def_with_set.iter() {
            self.define_params_with_set(param_def_with_set)
                .map_err(|define_params_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(define_params_error),
                        vec![],
                    )
                })?;
        }

        for dom_fact in have_fn_equal_stmt.fn_set_clause.dom_facts.iter() {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    RuntimeErrorStruct::exec_stmt_new_with_stmt(
                        have_fn_equal_stmt.clone().into(),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(store_fact_error)),
                        vec![],
                    )
                })?;
        }

        let equal_to_in_ret_set_atomic_fact = InFact::new(
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.fn_set_clause.ret_set.clone(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|verify_error| {
                RuntimeErrorStruct::exec_stmt_new_with_stmt(
                    have_fn_equal_stmt.clone().into(),
                    "".to_string(),
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_stmt: {} is not in return set {}",
                have_fn_equal_stmt.equal_to, have_fn_equal_stmt.fn_set_clause.ret_set
            );
            return Err(RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                have_fn_equal_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }

        Ok(())
    }
}
