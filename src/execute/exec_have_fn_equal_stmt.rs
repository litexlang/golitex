use crate::prelude::*;

use super::exec_have_fn_equal_shared::{
    build_curried_function_obj_from_layers, forall_binders_dom_and_curried_layers_from_fn_set_clause,
};

impl Runtime {
    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored = self
            .fn_set_from_fn_set_clause(&have_fn_equal_stmt.fn_set_clause)
            .map_err(|e| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: build fn set for storage failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        self.have_fn_equal_stmt_verify_well_defined(have_fn_equal_stmt, &fn_set_stored)
            .map_err(|e| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: verify well-defined failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let infer_result =
            self.store_have_fn_equal_stmt_facts(have_fn_equal_stmt, &fn_set_stored)?;

        Ok(
            (NonFactualStmtSuccess::new(have_fn_equal_stmt.clone().into(), infer_result, vec![]))
                .into(),
        )
    }

    fn have_fn_equal_stmt_forall_binders_dom_and_curried_layers(
        &self,
        clause: &FnSetClause,
    ) -> Result<(ParamDefWithType, Vec<Fact>, Vec<Vec<String>>), RuntimeError> {
        Ok(forall_binders_dom_and_curried_layers_from_fn_set_clause(
            clause,
        ))
    }

    fn store_have_fn_equal_stmt_facts(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        self.store_free_param_or_identifier_name(
            &have_fn_equal_stmt.name,
            ParamObjType::Identifier,
        )?;

        let function_identifier_obj: Obj =
            Identifier::new(have_fn_equal_stmt.name.clone()).into();
        let function_set_obj = fn_set_stored.clone().into();
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj.clone(),
            function_set_obj,
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();

        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(function_in_function_set_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        self.register_known_objs_in_fn_sets_for_element_body(
            &function_identifier_obj,
            fn_set_stored.body.clone(),
            Some(have_fn_equal_stmt.equal_to.clone()),
        );

        let (param_defs_with_type, forall_dom_facts, curried_layers) = self
            .have_fn_equal_stmt_forall_binders_dom_and_curried_layers(
                &have_fn_equal_stmt.fn_set_clause,
            )?;

        let function_obj =
            build_curried_function_obj_from_layers(&have_fn_equal_stmt.name, &curried_layers);

        let function_equals_equal_to_fact: AtomicFact = EqualFact::new(
            function_obj,
            have_fn_equal_stmt.equal_to.clone(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();

        let forall_fact = ForallFact::new(
            param_defs_with_type,
            forall_dom_facts,
            vec![function_equals_equal_to_fact.into()],
            have_fn_equal_stmt.line_file.clone(),
        );

        let to_store = self.inst_have_fn_forall_fact_for_store(forall_fact)?;

        let _ = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(to_store)
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        Ok(infer_result)
    }

    fn have_fn_equal_stmt_verify_well_defined(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.have_fn_equal_stmt_verify_well_defined_body(have_fn_equal_stmt, fn_set_stored)
        })
    }

    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);

        let function_set_obj = fn_set_stored.clone().into();
        self.verify_obj_well_defined_and_store_cache(&function_set_obj, &verify_state)
            .map_err(|well_defined_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        for param_def_with_set in have_fn_equal_stmt.fn_set_clause.params_def_with_set.iter() {
            self.define_params_with_set(param_def_with_set)
                .map_err(|define_params_error| {
                    short_exec_error(
                        have_fn_equal_stmt.clone().into(),
                        "",
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
                    short_exec_error(
                        have_fn_equal_stmt.clone().into(),
                        "",
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
        }

        let mut ret_set = have_fn_equal_stmt.fn_set_clause.ret_set.clone();
        let equal_to_for_in_fact = have_fn_equal_stmt.equal_to.clone();
        while let Obj::FnSet(inner) = ret_set {
            for param_def_with_set in inner.body.params_def_with_set.iter() {
                self.define_params_with_set(param_def_with_set)
                    .map_err(|define_params_error| {
                        short_exec_error(
                            have_fn_equal_stmt.clone().into(),
                            "",
                            Some(define_params_error),
                            vec![],
                        )
                    })?;
            }
            for dom_fact in inner.body.dom_facts.iter() {
                let _ = self
                    .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                        dom_fact.clone(),
                    )
                    .map_err(|store_fact_error| {
                        short_exec_error(
                            have_fn_equal_stmt.clone().into(),
                            "",
                            Some(store_fact_error),
                            vec![],
                        )
                    })?;
            }
            ret_set = (*inner.body.ret_set).clone();
        }

        let equal_to_in_ret_set_atomic_fact = InFact::new(
            equal_to_for_in_fact.clone(),
            ret_set.clone(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let verify_result = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|verify_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(verify_error),
                    vec![],
                )
            })?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_stmt: {} is not in return set {}",
                equal_to_for_in_fact, ret_set
            );
            return Err(short_exec_error(
                have_fn_equal_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }

        Ok(())
    }
}
