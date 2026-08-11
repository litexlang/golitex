use crate::prelude::*;
use std::collections::HashMap;

impl Runtime {
    pub fn exec_have_obj_equal_stmt(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_obj_equal_stmt_verify_well_definedness(have_obj_equal_stmt)?;
        let check_results = self.exec_have_obj_equal_stmt_verify_process(have_obj_equal_stmt)?;
        let infer_result = self.exec_have_obj_equal_stmt_affect_environment(have_obj_equal_stmt)?;

        Ok((NonFactualStmtSuccess::new(
            have_obj_equal_stmt.clone().into(),
            infer_result,
            check_results,
        ))
        .into())
    }

    /// Mathematical contract: an equality-backed object introduction has one
    /// defining value per declared parameter and meaningful dependent
    /// parameter types; value/type compatibility is proved immediately after
    /// this scope-construction check.
    fn exec_have_obj_equal_stmt_verify_well_definedness(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<(), RuntimeError> {
        if have_obj_equal_stmt.param_def.number_of_params()
            != have_obj_equal_stmt.objs_equal_to.len()
        {
            return Err(short_exec_error(
                have_obj_equal_stmt.clone().into(),
                "have_obj_equal_stmt: number of params in param_def does not match number of objs_equal_to"
                    .to_string(),
                None,
                vec![],
            ));
        }

        self.run_in_local_env(|rt| {
            rt.define_params_with_type(
                &have_obj_equal_stmt.param_def,
                false,
                ParamObjType::Identifier,
            )
            .map_err(|define_params_error| {
                short_exec_error(
                    have_obj_equal_stmt.clone().into(),
                    "",
                    Some(define_params_error),
                    vec![],
                )
            })?;
            Ok(())
        })
    }

    fn exec_have_obj_equal_stmt_verify_process(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut current_index = 0;
        let mut param_to_obj_map: HashMap<String, Obj> = HashMap::new();
        let mut check_results: Vec<StmtResult> = Vec::new();
        for param_def in have_obj_equal_stmt.param_def.groups.iter() {
            let current_type_holder = self
                .inst_param_type(
                    &param_def.param_type,
                    &param_to_obj_map,
                    ParamObjType::Identifier,
                )
                .map_err(|runtime_error| {
                    short_exec_error(
                        have_obj_equal_stmt.clone().into(),
                        "",
                        Some(runtime_error),
                        vec![],
                    )
                })?;
            let current_type = &current_type_holder;
            for name in param_def.params.iter() {
                let current_param_equal_to = &have_obj_equal_stmt.objs_equal_to[current_index];

                let mut verify_result = self
                    .verify_obj_satisfies_param_type(
                        current_param_equal_to.clone(),
                        current_type,
                        &UseContextVerifyState::new(0, false),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            have_obj_equal_stmt.clone().into(),
                            "",
                            Some(verify_error),
                            vec![],
                        )
                    })?;
                let mut known_source_sets = Vec::new();
                // A `have x T = y` declaration may transport `y` across a
                // propositionally equal indexed carrier.  Typical examples
                // are `FiniteList<A, m>` and `FiniteList<A, n>` after the
                // proof has established `m = n`.  Ordinary membership lookup
                // sees the source carrier recorded for `y`; recognize the
                // target carrier when those two set objects are already known
                // equal.
                if verify_result.is_unknown() {
                    if let ParamType::Obj(target_set) = current_type {
                        known_source_sets = self.known_sets_containing_obj(current_param_equal_to);
                        for source_set in known_source_sets.iter() {
                            let set_equality = self.verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(
                                &EqualFact::new(
                                    source_set.clone(),
                                    target_set.clone(),
                                    have_obj_equal_stmt.line_file.clone(),
                                )
                                .into(),
                            )?;
                            if !set_equality.is_unknown() {
                                verify_result = set_equality;
                                break;
                            }
                        }
                    }
                }
                if verify_result.is_unknown() {
                    // Error-only carrier provenance: when the expression's
                    // carrier was derived rather than stored as a direct
                    // membership fact, find the narrowest standard numeric
                    // carrier that the ordinary type checker can establish.
                    // This does not accept the failed declaration or store a
                    // new fact.
                    if known_source_sets.is_empty() {
                        for standard_set in [
                            StandardSet::NPos,
                            StandardSet::N,
                            StandardSet::Z,
                            StandardSet::Q,
                            StandardSet::R,
                            StandardSet::C,
                        ] {
                            let candidate_set: Obj = standard_set.into();
                            if candidate_set.to_string() == current_type.to_string() {
                                continue;
                            }
                            let candidate_type = ParamType::Obj(candidate_set.clone());
                            if let Ok(candidate_result) = self.verify_obj_satisfies_param_type(
                                current_param_equal_to.clone(),
                                &candidate_type,
                                &UseContextVerifyState::new(0, false),
                            ) {
                                if candidate_result.is_true() {
                                    known_source_sets.push(candidate_set);
                                    break;
                                }
                            }
                        }
                    }
                    let mut known_carriers = Vec::new();
                    for source_set in known_source_sets {
                        let source_text = source_set.to_string();
                        if !known_carriers.contains(&source_text) {
                            known_carriers.push(source_text);
                        }
                    }
                    let known_carrier_detail = if known_carriers.is_empty() {
                        "no source carrier is known".to_string()
                    } else {
                        format!("known carrier(s): {}", known_carriers.join(", "))
                    };
                    let msg = format!(
                        "have_obj_equal_stmt: carrier mismatch during verify_process: {} requires type {} for binding {}; {}; the binding was not stored",
                        current_param_equal_to,
                        current_type,
                        name,
                        known_carrier_detail,
                    );
                    return Err(short_exec_error(
                        have_obj_equal_stmt.clone().into(),
                        msg,
                        None,
                        vec![],
                    ));
                }
                check_results.push(verify_result);

                insert_symbol_substitution(
                    &mut param_to_obj_map,
                    name,
                    current_param_equal_to.clone(),
                );
                current_index += 1;
            }
        }

        Ok(check_results)
    }

    pub(crate) fn exec_have_obj_equal_stmt_affect_environment(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();

        let mut param_infer_result = if self.current_execution_is_trusted_file() {
            self.define_params_with_type_trusted(
                &have_obj_equal_stmt.param_def,
                ParamObjType::Identifier,
            )
        } else {
            // `verify_process` has already proved each right-hand side is in
            // its declared type. That proof is a witness of nonemptiness, so
            // requiring a separate prior nonempty fact would reject a first
            // concrete object of a newly defined structure.
            self.define_params_with_type(
                &have_obj_equal_stmt.param_def,
                false,
                ParamObjType::Identifier,
            )
        }
        .map_err(|define_params_error| {
            short_exec_error(
                have_obj_equal_stmt.clone().into(),
                "",
                Some(define_params_error),
                vec![],
            )
        })?;
        param_infer_result
            .relabel_all_added_facts_with_store_reason(HaveObjEqualStmt::store_reason());
        infer_result.new_infer_result_inside(param_infer_result);

        for (binding, obj) in have_obj_equal_stmt
            .param_def
            .collect_param_bindings()
            .iter()
            .zip(have_obj_equal_stmt.objs_equal_to.iter())
        {
            let equal_to_fact: AtomicFact = EqualFact::new(
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into(),
                obj.clone(),
                have_obj_equal_stmt.line_file.clone(),
            )
            .into();
            let equal_to_fact_infer_result = self
                .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    equal_to_fact,
                    HaveObjEqualStmt::store_reason(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        have_obj_equal_stmt.clone().into(),
                        "",
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(equal_to_fact_infer_result);
        }

        let lf = have_obj_equal_stmt.line_file.clone();
        for ((name, param_type), obj) in have_obj_equal_stmt
            .param_def
            .collect_param_names_with_types()
            .into_iter()
            .zip(have_obj_equal_stmt.objs_equal_to.iter())
        {
            match (param_type, obj) {
                (ParamType::Obj(Obj::FiniteSeqSet(fs)), Obj::FiniteSeqListObj(list)) => {
                    self.store_known_finite_seq_list_obj(
                        &name,
                        list.clone(),
                        Some(fs.clone()),
                        lf.clone(),
                    );
                }
                (ParamType::Obj(Obj::MatrixSet(ms)), Obj::MatrixListObj(m)) => {
                    self.store_known_matrix_list_obj(
                        &name,
                        m.clone(),
                        Some(ms.clone()),
                        lf.clone(),
                    );
                }
                _ => {}
            }
        }

        Ok(infer_result)
    }

    pub(crate) fn exec_have_obj_equal_stmt_affect_environment_only(
        &mut self,
        have_obj_equal_stmt: &HaveObjEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_have_obj_equal_stmt_affect_environment(have_obj_equal_stmt)?;
        Ok(
            NonFactualStmtSuccess::new(have_obj_equal_stmt.clone().into(), infer_result, vec![])
                .into(),
        )
    }
}
