use crate::prelude::*;

use super::exec_have_fn_equal_shared::{
    build_function_obj_with_param_names, forall_param_defs_dom_and_map_from_have_fn_clause,
};

impl Runtime {
    pub fn exec_have_fn_equal_case_by_case_stmt(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored = self.exec_have_fn_equal_case_by_case_stmt_verify_well_definedness(
            have_fn_equal_case_by_case_stmt,
        )?;
        let inside_results = self
            .exec_have_fn_equal_case_by_case_stmt_verify_process(have_fn_equal_case_by_case_stmt)?;
        let infer_result = self.exec_have_fn_equal_case_by_case_stmt_affect_environment(
            have_fn_equal_case_by_case_stmt,
            &fn_set_stored,
        )?;

        Ok((NonFactualStmtSuccess::new(
            have_fn_equal_case_by_case_stmt.clone().into(),
            infer_result,
            inside_results,
        ))
        .into())
    }

    pub(crate) fn store_have_fn_equal_case_by_case_stmt_facts(
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
            .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                function_in_function_set_fact,
                InferReason::FunctionDefinition,
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_case_by_case_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let (param_defs_with_type, base_forall_dom_facts, fn_set_param_to_forall_param) =
            forall_param_defs_dom_and_map_from_have_fn_clause(
                self,
                &have_fn_equal_case_by_case_stmt.fn_set_clause,
            )?;
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

            let mut forall_dom_facts: Vec<Fact> =
                Vec::with_capacity(base_forall_dom_facts.len() + 1);
            forall_dom_facts.extend(base_forall_dom_facts.iter().cloned());
            forall_dom_facts.push(
                self.inst_and_chain_atomic_fact(
                    case_fact,
                    &fn_set_param_to_forall_param,
                    ParamObjType::FnSet,
                    None,
                )?
                .into(),
            );

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
            )?;
            let forall_as_fact = self
                .inst_have_fn_forall_fact_for_store(forall_fact)
                .map_err(|store_inst_error| {
                    short_exec_error(
                        have_fn_equal_case_by_case_stmt.clone().into(),
                        "have_fn_equal_case_by_case_stmt: inst forall for store failed".to_string(),
                        Some(store_inst_error),
                        vec![],
                    )
                })?;

            let forall_infer_result = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                    forall_as_fact,
                    InferReason::FunctionDefinition,
                )
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

    fn exec_have_fn_equal_case_by_case_stmt_verify_well_definedness(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<FnSet, RuntimeError> {
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

        Ok(fn_set_stored)
    }

    fn exec_have_fn_equal_case_by_case_stmt_verify_process(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut inside_results = Vec::new();
        for case_index in 0..have_fn_equal_case_by_case_stmt.cases.len() {
            let case_fact = &have_fn_equal_case_by_case_stmt.cases[case_index];
            let equal_to = &have_fn_equal_case_by_case_stmt.equal_tos[case_index];

            let result = self.run_in_local_env(|rt| {
                rt.have_fn_equal_case_by_case_stmt_verify_well_defined_body(
                    have_fn_equal_case_by_case_stmt,
                    case_fact,
                    equal_to,
                )
            })?;
            inside_results.push(result);
        }

        Ok(inside_results)
    }

    fn exec_have_fn_equal_case_by_case_stmt_affect_environment(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        let infer_result = self.store_have_fn_equal_case_by_case_stmt_facts(
            have_fn_equal_case_by_case_stmt,
            fn_set_stored,
        )?;
        if have_fn_equal_case_by_case_stmt.as_algo {
            self.exec_have_fn_equal_case_by_case_stmt_as_algo(have_fn_equal_case_by_case_stmt)?;
        }

        Ok(infer_result)
    }

    pub(crate) fn exec_have_fn_equal_case_by_case_stmt_affect_environment_only(
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
        let infer_result = self.exec_have_fn_equal_case_by_case_stmt_affect_environment(
            have_fn_equal_case_by_case_stmt,
            &fn_set_stored,
        )?;
        Ok(NonFactualStmtSuccess::new(
            have_fn_equal_case_by_case_stmt.clone().into(),
            infer_result,
            vec![],
        )
        .into())
    }

    fn have_fn_equal_case_by_case_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_case_by_case_stmt: &HaveFnEqualCaseByCaseStmt,
        case_fact: &AndChainAtomicFact,
        equal_to: &Obj,
    ) -> Result<StmtResult, RuntimeError> {
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
            .verify_well_defined_and_store_and_infer_with_default_verify_state(case_fact_as_fact)
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

        Ok(verify_result)
    }
}
