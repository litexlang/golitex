use crate::prelude::*;
use std::collections::HashMap;

fn fn_set_equality_fact(left: &FnSet, right: &FnSet, line_file: LineFile) -> Fact {
    EqualFact::new(left.clone().into(), right.clone().into(), line_file).into()
}

fn fn_set_equality_verify_error(
    left: &FnSet,
    right: &FnSet,
    line_file: LineFile,
    message: String,
    cause: Option<RuntimeError>,
) -> RuntimeError {
    {
        VerifyRuntimeError(RuntimeErrorStruct::new(
            Some(fn_set_equality_fact(left, right, line_file.clone()).into_stmt()),
            message,
            line_file,
            cause,
            vec![],
        ))
        .into()
    }
}

fn fn_set_equality_verified_by_builtin_rules_result(
    left: &FnSet,
    right: &FnSet,
    line_file: LineFile,
) -> StmtResult {
    let stmt = fn_set_equality_fact(left, right, line_file);
    StmtResult::FactualStmtSuccess(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            stmt,
            "fnset equality: mutual implication of param sets, dom facts, and ret set".to_string(),
            Vec::new(),
        ),
    )
}

impl Runtime {
    pub fn verify_fn_set_with_params_equality_by_builtin_rules(
        &mut self,
        left: &FnSet,
        right: &FnSet,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if ParamGroupWithSet::number_of_params(&left.body.params_def_with_set)
            != ParamGroupWithSet::number_of_params(&right.body.params_def_with_set)
        {
            return Ok((StmtUnknown::new()).into());
        }

        let left_implies_right = self.verify_fn_set_with_params_directionally_in_local_env(
            left,
            right,
            line_file.clone(),
            verify_state,
        )?;
        if !left_implies_right {
            return Ok((StmtUnknown::new()).into());
        }

        let right_implies_left = self.verify_fn_set_with_params_directionally_in_local_env(
            right,
            left,
            line_file.clone(),
            verify_state,
        )?;
        if !right_implies_left {
            return Ok((StmtUnknown::new()).into());
        }

        Ok(fn_set_equality_verified_by_builtin_rules_result(
            left, right, line_file,
        ))
    }

    fn verify_fn_set_with_params_directionally_in_local_env(
        &mut self,
        source: &FnSet,
        target: &FnSet,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.verify_fn_set_with_params_directionally_in_local_env_body(
                source,
                target,
                line_file,
                verify_state,
            )
        })
    }

    fn verify_fn_set_with_params_directionally_in_local_env_body(
        &mut self,
        source: &FnSet,
        target: &FnSet,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let target_flat_param_names =
            ParamGroupWithSet::collect_param_names(&target.body.params_def_with_set);
        let generated_param_names =
            self.generate_random_unused_names(target_flat_param_names.len());
        let source_param_to_generated_arg_map = self
            .define_directional_source_fn_set_params_in_local_env(
                source,
                &generated_param_names,
                target,
                line_file.clone(),
            )?;
        let target_param_to_generated_arg_map = Self::build_param_to_generated_arg_map(
            &target_flat_param_names,
            &generated_param_names,
        );

        self.assume_directional_source_fn_set_dom_facts_in_local_env(
            source,
            &source_param_to_generated_arg_map,
            target,
            line_file.clone(),
        )?;

        if !self.verify_directional_target_fn_set_param_membership_facts(
            source,
            target,
            &target_param_to_generated_arg_map,
            line_file.clone(),
            verify_state,
        )? {
            return Ok(false);
        }

        if !self.verify_directional_target_fn_set_dom_facts(
            source,
            target,
            line_file.clone(),
            &target_param_to_generated_arg_map,
            verify_state,
        )? {
            return Ok(false);
        }

        let source_ret_set = self
            .inst_obj(
                &source.body.ret_set,
                &source_param_to_generated_arg_map,
                ParamObjType::FnSet,
            )
            .map_err(|e| {
                fn_set_equality_verify_error(
                    source,
                    target,
                    line_file.clone(),
                    "failed to instantiate source ret set for fnset equality check".to_string(),
                    Some(e),
                )
            })?;
        let target_ret_set = self
            .inst_obj(
                &target.body.ret_set,
                &target_param_to_generated_arg_map,
                ParamObjType::FnSet,
            )
            .map_err(|e| {
                fn_set_equality_verify_error(
                    source,
                    target,
                    line_file.clone(),
                    "failed to instantiate target ret set for fnset equality check".to_string(),
                    Some(e),
                )
            })?;
        let ret_equal_fact = EqualFact::new(source_ret_set, target_ret_set, line_file);
        let ret_equal_result = self.verify_equal_fact(&ret_equal_fact, verify_state)?;
        Ok(ret_equal_result.is_true())
    }

    fn build_param_to_generated_arg_map(
        flat_param_names: &[String],
        generated_param_names: &[String],
    ) -> HashMap<String, Obj> {
        let mut param_to_generated_arg_map: HashMap<String, Obj> =
            HashMap::with_capacity(flat_param_names.len());
        for (param_name, generated_param_name) in
            flat_param_names.iter().zip(generated_param_names.iter())
        {
            param_to_generated_arg_map.insert(
                param_name.clone(),
                obj_for_bound_param_in_scope(generated_param_name.clone(), ParamObjType::FnSet),
            );
        }
        param_to_generated_arg_map
    }

    /// Rename `fn_set` parameters in flat order to `generated_flat_names` (headers, param sets,
    /// `dom_facts`, `ret_set`). For comparing two alpha-equivalent signatures, call with the **same**
    /// list from one `generate_random_unused_names` (or similar) on both `FnSet`s.
    pub(crate) fn fn_set_alpha_renamed_for_display_compare(
        &self,
        fn_set: &FnSetBody,
        generated_flat_names: &[String],
    ) -> Result<Obj, RuntimeError> {
        let flat = ParamGroupWithSet::collect_param_names(&fn_set.params_def_with_set);
        if flat.len() != generated_flat_names.len() {
            return Err(
                VerifyRuntimeError(RuntimeErrorStruct::new_with_just_msg("internal: fn_set alpha rename requires generated_flat_names len == flat param count"
                        .to_string()))
                .into(),
            );
        }
        let map = Self::build_param_to_generated_arg_map(&flat, generated_flat_names);
        let mut new_params = Vec::with_capacity(fn_set.params_def_with_set.len());
        let mut c_idx: usize = 0;
        for g in fn_set.params_def_with_set.iter() {
            let n = g.params.len();
            let names = generated_flat_names[c_idx..c_idx + n].to_vec();
            c_idx += n;
            let new_set = self.inst_obj(g.set_obj(), &map, ParamObjType::FnSet)?;
            new_params.push(ParamGroupWithSet::new(names, new_set));
        }
        let mut new_dom = Vec::with_capacity(fn_set.dom_facts.len());
        for d in fn_set.dom_facts.iter() {
            new_dom.push(self.inst_or_and_chain_atomic_fact(d, &map, ParamObjType::FnSet, None)?);
        }
        let new_ret = self.inst_obj(fn_set.ret_set.as_ref(), &map, ParamObjType::FnSet)?;
        Ok(FnSet::new(new_params, new_dom, new_ret)?.into())
    }

    fn define_directional_source_fn_set_params_in_local_env(
        &mut self,
        source: &FnSet,
        generated_param_names: &[String],
        target: &FnSet,
        line_file: LineFile,
    ) -> Result<HashMap<String, Obj>, RuntimeError> {
        let mut source_param_to_generated_arg_map: HashMap<String, Obj> =
            HashMap::with_capacity(generated_param_names.len());
        let mut flat_index: usize = 0;

        for param_def_with_set in source.body.params_def_with_set.iter() {
            let next_flat_index = flat_index + param_def_with_set.params.len();
            let generated_names_for_current_group =
                generated_param_names[flat_index..next_flat_index].to_vec();
            let instantiated_param_set = self
                .inst_obj(
                    param_def_with_set.set_obj(),
                    &source_param_to_generated_arg_map,
                    ParamObjType::FnSet,
                )
                .map_err(|e| {
                    fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "failed to instantiate source fnset param set".to_string(),
                        Some(e),
                    )
                })?;
            let generated_param_def = ParamGroupWithSet::new(
                generated_names_for_current_group.clone(),
                instantiated_param_set,
            );
            self.define_params_with_set(&generated_param_def)
                .map_err(|e| {
                    fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "failed to define fresh params for directional fnset equality verification"
                            .to_string(),
                        Some(e),
                    )
                })?;

            for (source_param_name, generated_param_name) in param_def_with_set
                .params
                .iter()
                .zip(generated_names_for_current_group.iter())
            {
                source_param_to_generated_arg_map.insert(
                    source_param_name.clone(),
                    obj_for_bound_param_in_scope(generated_param_name.clone(), ParamObjType::FnSet),
                );
            }
            flat_index = next_flat_index;
        }

        Ok(source_param_to_generated_arg_map)
    }

    fn assume_directional_source_fn_set_dom_facts_in_local_env(
        &mut self,
        source: &FnSet,
        source_param_to_generated_arg_map: &HashMap<String, Obj>,
        target: &FnSet,
        line_file: LineFile,
    ) -> Result<(), RuntimeError> {
        for dom_fact in source.body.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    source_param_to_generated_arg_map,
                    ParamObjType::FnSet,
                    None,
                )
                .map_err(|e| {
                    fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "failed to instantiate source fnset dom fact".to_string(),
                        Some(e),
                    )
                })?;
            self.store_exist_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                instantiated_dom_fact.into(),
            )
            .map_err(|e| {
                fn_set_equality_verify_error(
                    source,
                    target,
                    line_file.clone(),
                    "failed to assume source fnset dom fact in local equality environment"
                        .to_string(),
                    Some(e),
                )
            })?;
        }
        Ok(())
    }

    fn verify_directional_target_fn_set_param_membership_facts(
        &mut self,
        source: &FnSet,
        target: &FnSet,
        target_param_to_generated_arg_map: &HashMap<String, Obj>,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        for param_def_with_set in target.body.params_def_with_set.iter() {
            let instantiated_param_type = ParamType::Obj(
                self.inst_obj(
                    param_def_with_set.set_obj(),
                    target_param_to_generated_arg_map,
                    ParamObjType::FnSet,
                )
                .map_err(|e| {
                    fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "failed to instantiate target fnset param set".to_string(),
                        Some(e),
                    )
                })?,
            );
            for param_name in param_def_with_set.params.iter() {
                let Some(generated_param_obj) =
                    target_param_to_generated_arg_map.get(param_name).cloned()
                else {
                    return Err(fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "internal error: missing generated param while verifying fnset equality"
                            .to_string(),
                        None,
                    ));
                };
                let verify_result = self.verify_obj_satisfies_param_type(
                    generated_param_obj,
                    &instantiated_param_type,
                    verify_state,
                )?;
                if !verify_result.is_true() {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    fn verify_directional_target_fn_set_dom_facts(
        &mut self,
        source: &FnSet,
        target: &FnSet,
        line_file: LineFile,
        target_param_to_generated_arg_map: &HashMap<String, Obj>,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        for dom_fact in target.body.dom_facts.iter() {
            let instantiated_dom_fact = self
                .inst_or_and_chain_atomic_fact(
                    dom_fact,
                    target_param_to_generated_arg_map,
                    ParamObjType::FnSet,
                    None,
                )
                .map_err(|e| {
                    fn_set_equality_verify_error(
                        source,
                        target,
                        line_file.clone(),
                        "failed to instantiate target fnset dom fact".to_string(),
                        Some(e),
                    )
                })?;
            let verify_result =
                self.verify_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
            if !verify_result.is_true() {
                return Ok(false);
            }
        }
        Ok(true)
    }
}
