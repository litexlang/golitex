use crate::prelude::*;
use std::collections::HashMap;

use super::exec_have_fn_equal_shared::build_curried_function_obj_from_layers;

impl Runtime {
    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored = self
            .add_mangled_prefix_to_fn_set_clause(
                &have_fn_equal_stmt.fn_set_clause,
                have_fn_equal_stmt.line_file.clone(),
            )
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
    ) -> Result<
        (
            ParamDefWithType,
            Vec<Fact>,
            Vec<Vec<String>>,
        ),
        RuntimeError,
    > {
        let mut type_groups: Vec<ParamGroupWithParamType> = Vec::new();
        let mut dom_facts: Vec<Fact> = Vec::new();
        let mut layers: Vec<Vec<String>> = Vec::new();

        for pg in clause.params_def_with_set.iter() {
            type_groups.push(ParamGroupWithParamType::new(
                pg.params.clone(),
                ParamType::Obj(pg.set.clone()),
            ));
        }
        for d in clause.dom_facts.iter() {
            let f: OrAndChainAtomicFact = d.clone();
            dom_facts.push(f.into());
        }
        layers.push(ParamGroupWithSet::collect_param_names(
            &clause.params_def_with_set,
        ));

        let mut ret_set = clause.ret_set.clone();
        while let Obj::FnSet(inner) = ret_set {
            let mut dem_map: HashMap<String, Obj> = HashMap::new();
            for pg in inner.params_def_with_set.iter() {
                for p in pg.params.iter() {
                    if let Some(user_param) =
                        p.strip_prefix(DEFAULT_MANGLED_FN_PARAM_PREFIX)
                    {
                        if !user_param.is_empty() {
                            dem_map.insert(p.clone(), user_param.to_string().into());
                        }
                    }
                }
            }

            for pg in inner.params_def_with_set.iter() {
                let user_params: Vec<String> = pg
                    .params
                    .iter()
                    .map(|p| {
                        p.strip_prefix(DEFAULT_MANGLED_FN_PARAM_PREFIX)
                            .filter(|s| !s.is_empty())
                            .map(String::from)
                            .unwrap_or_else(|| p.clone())
                    })
                    .collect();
                type_groups.push(ParamGroupWithParamType::new(
                    user_params,
                    ParamType::Obj(pg.set.clone()),
                ));
            }

            for d in inner.dom_facts.iter() {
                let inst = self.inst_or_and_chain_atomic_fact(d, &dem_map, FreeParamObjType::FnSet)?;
                let f: OrAndChainAtomicFact = inst;
                dom_facts.push(f.into());
            }

            let layer_names: Vec<String> = inner
                .params_def_with_set
                .iter()
                .flat_map(|pg| pg.params.iter())
                .map(|p| {
                    p.strip_prefix(DEFAULT_MANGLED_FN_PARAM_PREFIX)
                        .filter(|s| !s.is_empty())
                        .map(String::from)
                        .unwrap_or_else(|| p.clone())
                })
                .collect();
            layers.push(layer_names);

            ret_set = (*inner.ret_set).clone();
        }

        Ok((ParamDefWithType::new(type_groups), dom_facts, layers))
    }

    fn store_have_fn_equal_stmt_facts(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
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
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

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
        let forall_as_fact: Fact = forall_fact.into();
        let forall_infer_result = self
            .store_fact_without_well_defined_verified_and_infer(forall_as_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        infer_result.new_infer_result_inside(forall_infer_result);

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
        let mut equal_to_for_in_fact = have_fn_equal_stmt.equal_to.clone();
        while let Obj::FnSet(inner) = ret_set {
            for param_def_with_set in inner.params_def_with_set.iter() {
                self.define_params_with_set(param_def_with_set)
                    .map_err(|define_params_error| {
                        short_exec_error(
                            have_fn_equal_stmt.clone().into(),
                            "",
                            Some(define_params_error),
                            vec![],
                        )
                    })?;
                // Nested `fn` in ret_set uses mangled stored names (`__x`); RHS of `=` still has `x`.
                let mut user_to_mangled: HashMap<String, Obj> = HashMap::new();
                for stored_param in param_def_with_set.params.iter() {
                    if let Some(user_param) =
                        stored_param.strip_prefix(DEFAULT_MANGLED_FN_PARAM_PREFIX)
                    {
                        if user_param.is_empty() {
                            continue;
                        }
                        user_to_mangled.insert(user_param.to_string(), stored_param.clone().into());
                    }
                }
                if !user_to_mangled.is_empty() {
                    equal_to_for_in_fact = self
                        .inst_obj(&equal_to_for_in_fact, &user_to_mangled, FreeParamObjType::FnSet)
                        .map_err(|e| {
                            short_exec_error(
                                have_fn_equal_stmt.clone().into(),
                                "",
                                Some(e),
                                vec![],
                            )
                        })?;
                }
            }
            for dom_fact in inner.dom_facts.iter() {
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
            ret_set = (*inner.ret_set).clone();
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
