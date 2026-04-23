use crate::prelude::*;

use super::exec_have_fn_equal_shared::{
    build_function_obj_with_param_names, inst_have_fn_forall_fact_for_store,
    param_defs_with_type_from_have_fn_clause,
};

impl Runtime {
    pub fn exec_have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored = self
            .fn_set_from_fn_set_clause(&have_fn_equal_case_by_case_stmt.fn_set_clause)
            .map_err(|e| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "have_fn_equal_case_by_case_stmt: build fn set for storage failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        self.have_fn_equal_case_by_case_stmt_verify_well_defined(
            have_fn_equal_case_by_case_stmt,
            &fn_set_stored,
        )
        .map_err(|e| {
            short_exec_error(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "have_fn_equal_case_by_case_stmt: verify well-defined failed".to_string(),
                Some(e),
                vec![],
            )
        })?;

        let infer_result = self.store_have_fn_equal_case_by_case_stmt_facts(
            have_fn_equal_case_by_case_stmt,
            &fn_set_stored,
        )?;
        Ok((NonFactualStmtSuccess::new(
            have_fn_equal_case_by_case_stmt.clone().into(),
            infer_result,
            vec![],
        ))
        .into())
    }

    fn store_have_fn_equal_case_by_case_stmt_facts(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        self.store_free_param_or_identifier_name(
            &have_fn_equal_case_by_case_stmt.name,
            ParamObjType::Identifier,
        )?;

        let function_identifier_obj =
            Identifier::new(have_fn_equal_case_by_case_stmt.name.clone()).into();
        let function_set_obj = fn_set_stored.clone().into();
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj,
            function_set_obj,
            have_fn_equal_case_by_case_stmt.line_file.clone(),
        )
        .into();

        let mut infer_result = self
            .verify_well_defined_and_store_and_infer_with_final_round_verify_state(function_in_function_set_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let param_defs_with_type = param_defs_with_type_from_have_fn_clause(
            &have_fn_equal_case_by_case_stmt.fn_set_clause,
        );
        let param_names = ParamGroupWithSet::collect_param_names(
            &have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .params_def_with_set,
        );
        let function_obj = build_function_obj_with_param_names(
            &have_fn_equal_case_by_case_stmt.name,
            &param_names,
        );

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            let mut forall_dom_facts: Vec<Fact> = Vec::with_capacity(
                have_fn_equal_case_by_case_stmt
                    .fn_set_clause
                    .dom_facts
                    .len()
                    + 1,
            );
            for dom_fact in have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .dom_facts
                .iter()
            {
                forall_dom_facts.push(dom_fact.clone().into());
            }
            forall_dom_facts.push(case_fact.clone().into());

            let function_equals_equal_to_fact: AtomicFact = EqualFact::new(
                function_obj.clone(),
                equal_to.clone(),
                have_fn_equal_case_by_case_stmt.line_file.clone(),
            )
            .into();
            let forall_fact = ForallFact::new(
                param_defs_with_type.clone(),
                forall_dom_facts,
                vec![function_equals_equal_to_fact.into()],
                have_fn_equal_case_by_case_stmt.line_file.clone(),
            );
            let forall_as_fact = inst_have_fn_forall_fact_for_store(self, forall_fact).map_err(
                |store_inst_error| {
                    short_exec_error(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "have_fn_equal_case_by_case_stmt: inst forall for store failed".to_string(),
                        Some(store_inst_error),
                        vec![],
                    )
                },
            )?;

            let forall_infer_result = self
                .verify_well_defined_and_store_and_infer_with_final_round_verify_state(forall_as_fact)
                .map_err(|store_fact_error| {
                    short_exec_error(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "",
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(forall_infer_result);
        }

        Ok(infer_result)
    }

    fn have_fn_equal_case_by_case_stmt_verify_well_defined(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeError> {
        if have_fn_equal_case_by_case_stmt.cases.len()
            != have_fn_equal_case_by_case_stmt.equal_tos.len()
        {
            return Err(short_exec_error(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "have_fn_equal_case_by_case_stmt: number of cases does not match number of equal_tos"
                    .to_string(),
                None,
                vec![],
            ));
        }

        let function_set_obj = fn_set_stored.clone().into();
        self.verify_obj_well_defined_and_store_cache(
            &function_set_obj,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                have_fn_equal_case_by_case_stmt.clone().into(),
                "",
                Some(well_defined_error),
                vec![],
            )
        })?;

        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            self.run_in_local_env(|rt| {
                rt.have_fn_equal_case_by_case_stmt_verify_well_defined_body(
                    have_fn_equal_case_by_case_stmt,
                    case_fact,
                    equal_to,
                )
            })?;
        }

        Ok(())
    }

    fn have_fn_equal_case_by_case_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        case_fact: &AndChainAtomicFact,
        equal_to: &Obj,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let case_fact_as_fact: Fact = case_fact.clone().into();

        for param_def_with_set in have_fn_equal_case_by_case_stmt
            .fn_set_clause
            .params_def_with_set
            .iter()
        {
            self.define_params_with_set(param_def_with_set)
                .map_err(|define_params_error| {
                    short_exec_error(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "",
                        Some(define_params_error),
                        vec![],
                    )
                })?;
        }

        for dom_fact in have_fn_equal_case_by_case_stmt
            .fn_set_clause
            .dom_facts
            .iter()
        {
            let _ = self
                .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "",
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
        }

        let _ = self
            .verify_well_defined_and_store_and_infer_with_final_round_verify_state(case_fact_as_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        self.verify_obj_well_defined_and_store_cache(equal_to, &verify_state)
            .map_err(|well_defined_error| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "",
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        let equal_to_in_ret_set_atomic_fact = InFact::new(
            equal_to.clone(),
            have_fn_equal_case_by_case_stmt
                .fn_set_clause
                .ret_set
                .clone(),
            have_fn_equal_case_by_case_stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "",
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_case_by_case_stmt: {} is not in return set {} under case {}",
                equal_to, have_fn_equal_case_by_case_stmt.fn_set_clause.ret_set, case_fact,
            );
            return Err(short_exec_error(
                have_fn_equal_case_by_case_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }

        Ok(())
    }
}
