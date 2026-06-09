use crate::prelude::*;
use std::collections::HashMap;
use std::result::Result;

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&exist_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_exist_fact_well_defined(exist_fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(exist_fact.clone()).into_stmt()),
                        String::new(),
                        exist_fact.line_file(),
                        Some(e),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        let result = self.verify_exist_fact_with_known_exist_fact(exist_fact, exist_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        if verify_state.is_round_0() {
            let result = self.verify_exist_fact_with_known_forall(exist_fact, verify_state)?;
            if result.is_true() {
                return Ok(result);
            }

            if exist_fact.is_exist_unique() {
                if let Some(proved) = self.try_verify_exist_unique_by_exist_and_uniqueness_forall(
                    exist_fact,
                    verify_state,
                )? {
                    return Ok(proved);
                }
            }
        }

        Ok(StmtUnknown::new().into())
    }

    pub(crate) fn build_exist_unique_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, false)
    }

    pub(crate) fn build_exist_unique_component_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFactEnum,
    ) -> Result<ForallFact, RuntimeError> {
        self.build_exist_unique_uniqueness_forall_fact_inner(exist_fact, true)
    }

    fn build_exist_unique_uniqueness_forall_fact_inner(
        &self,
        exist_fact: &ExistFactEnum,
        component_conclusion: bool,
    ) -> Result<ForallFact, RuntimeError> {
        let lf = exist_fact.line_file();
        let flat_orig = exist_fact.params_def_with_type().collect_param_names();
        let n = flat_orig.len();
        let flat_a: Vec<String> = flat_orig.iter().map(|name| format!("{}1", name)).collect();
        let flat_b: Vec<String> = flat_orig.iter().map(|name| format!("{}2", name)).collect();

        let mut map_running_a: HashMap<String, Obj> = HashMap::new();
        let mut map_running_b: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_a: Vec<String> = group
                .params
                .iter()
                .map(|name| format!("{}1", name))
                .collect();
            for (orig, nm) in group.params.iter().zip(chunk_a.iter()) {
                map_running_a.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Forall),
                );
            }
            let pt_a =
                self.inst_param_type(&group.param_type, &map_running_a, ParamObjType::Forall)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_a, pt_a));
        }
        for group in exist_fact.params_def_with_type().groups.iter() {
            let chunk_b: Vec<String> = group
                .params
                .iter()
                .map(|name| format!("{}2", name))
                .collect();
            for (orig, nm) in group.params.iter().zip(chunk_b.iter()) {
                map_running_b.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Forall),
                );
            }
            let pt_b =
                self.inst_param_type(&group.param_type, &map_running_b, ParamObjType::Forall)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_b, pt_b));
        }

        let map_a: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_a
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall)),
            )
            .collect();
        let map_b: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_b
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall)),
            )
            .collect();

        // Witness parameters in `exist_fact.facts` are [`ExistFreeParamObj`]; only `inst_*` with
        // [`ParamObjType::Exist`] substitutes them from `map_a` / `map_b` into the forall copies.
        let mut dom_facts: Vec<Fact> = Vec::new();
        for inner in exist_fact.facts().iter() {
            let f_a = self.inst_exist_body_fact(inner, &map_a, ParamObjType::Exist, None)?;
            dom_facts.push(f_a.to_fact());
        }
        for inner in exist_fact.facts().iter() {
            let f_b = self.inst_exist_body_fact(inner, &map_b, ParamObjType::Exist, None)?;
            dom_facts.push(f_b.to_fact());
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        if n == 1 {
            let eq = EqualFact::new(
                obj_for_bound_param_in_scope(flat_a[0].clone(), ParamObjType::Forall),
                obj_for_bound_param_in_scope(flat_b[0].clone(), ParamObjType::Forall),
                lf.clone(),
            );
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        } else if component_conclusion {
            let mut equal_facts: Vec<AtomicFact> = Vec::new();
            for (left_name, right_name) in flat_a.iter().zip(flat_b.iter()) {
                equal_facts.push(
                    EqualFact::new(
                        obj_for_bound_param_in_scope(left_name.clone(), ParamObjType::Forall),
                        obj_for_bound_param_in_scope(right_name.clone(), ParamObjType::Forall),
                        lf.clone(),
                    )
                    .into(),
                );
            }
            then_facts.push(AndFact::new(equal_facts, lf.clone()).into());
        } else {
            let left_tuple: Obj = Tuple::new(
                flat_a
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let right_tuple: Obj = Tuple::new(
                flat_b
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Forall))
                    .collect::<Vec<Obj>>(),
            )
            .into();
            let eq = EqualFact::new(left_tuple, right_tuple, lf.clone());
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
        }

        let forall_fact = ForallFact::new(
            ParamDefWithType::new(forall_groups),
            dom_facts,
            then_facts,
            lf,
        )?;

        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        for group in forall_fact.params_def_with_type.groups.iter() {
            for param in group.params.iter() {
                param_to_arg_map
                    .insert(param.clone(), ForallFreeParamObj::new(param.clone()).into());
            }
        }

        let forall_fact = self.inst_fact(
            &forall_fact.into(),
            &param_to_arg_map,
            ParamObjType::Forall,
            None,
        )?;

        match forall_fact {
            Fact::ForallFact(x) => Ok(x.clone()),
            _ => {
                unreachable!();
            }
        }
    }

    fn try_verify_exist_unique_by_exist_and_uniqueness_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if exist_fact.params_def_with_type().number_of_params() == 0 {
            return Ok(None);
        }
        let plain = ExistFactEnum::ExistFact(ExistFactBody::new(
            exist_fact.params_def_with_type().clone(),
            exist_fact.facts().clone(),
            exist_fact.line_file(),
        )?);
        let wd_ok = verify_state.make_state_with_req_ok_set_to_true();
        let plain_res = self.verify_exist_fact(&plain, &wd_ok)?;
        if !plain_res.is_true() {
            return Ok(None);
        }

        let uniqueness_forall = self.build_exist_unique_uniqueness_forall_fact(exist_fact)?;

        let uniqueness_fact: Fact = uniqueness_forall.clone().into();
        let uniq_res = self.verify_fact(&uniqueness_fact, &wd_ok)?;
        if !uniq_res.is_true() {
            return Ok(None);
        }

        let mut infers = InferResult::new();
        infers.new_fact(&exist_fact.clone().into());
        infers.new_infer_result_inside(stmt_result_infers(&plain_res));
        infers.new_infer_result_inside(stmt_result_infers(&uniq_res));
        infers.new_fact(&uniqueness_fact);

        let out = FactualStmtSuccess::new_with_verified_by_known_fact_and_infer(
            exist_fact.clone().into(),
            infers,
            VerifiedByResult::cited_fact(
                exist_fact.clone().into(),
                uniqueness_fact.clone(),
                Some("exist!: witness exist and uniqueness forall verified".to_string()),
            ),
            vec![],
        );
        Ok(Some(out.into()))
    }

    pub fn verify_exist_fact_with_known_exist_fact(
        &mut self,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        for environment in self.iter_environments_from_top() {
            let result = Self::verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
                self,
                environment,
                exist_fact,
                known_exist_fact,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_exist_fact_with_known_exist_fact_with_facts_in_environment(
        runtime: &Runtime,
        environment: &Environment,
        exist_fact: &ExistFactEnum,
        known_exist_fact: &ExistFactEnum,
    ) -> Result<StmtResult, RuntimeError> {
        let goal_keys = Self::known_exist_lookup_keys(known_exist_fact);
        let target_body_string = Self::exist_fact_normalized_body_string(runtime, exist_fact)
            .map_err(|e| {
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(exist_fact.clone()).into_stmt()),
                    String::new(),
                    exist_fact.line_file(),
                    Some(e),
                    vec![],
                )))
            })?;
        for key in goal_keys.iter() {
            let Some(known_exist_facts) = environment.known_exist_facts.get(key) else {
                continue;
            };
            for known_fact in known_exist_facts.iter() {
                if !known_fact.can_be_used_to_verify_goal(exist_fact) {
                    continue;
                }
                let known_body_string =
                    Self::exist_fact_normalized_body_string(runtime, known_fact).map_err(|e| {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(exist_fact.clone()).into_stmt()),
                            String::new(),
                            exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    })?;
                if target_body_string == known_body_string {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
                        exist_fact.clone().into(),
                        VerifiedByResult::cited_fact(
                            exist_fact.clone().into(),
                            known_fact.clone().into(),
                            None,
                        ),
                        Vec::new(),
                    ))
                    .into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn known_exist_lookup_keys(goal: &ExistFactEnum) -> Vec<String> {
        let mut keys = vec![goal.key()];
        if let ExistFactEnum::ExistFact(body) = goal {
            keys.push(ExistFactEnum::ExistUniqueFact(body.clone()).key());
        }
        keys.sort();
        keys.dedup();
        keys
    }

    fn exist_fact_normalized_body_string(
        runtime: &Runtime,
        exist_fact: &ExistFactEnum,
    ) -> Result<String, RuntimeError> {
        let mut param_to_arg_map: HashMap<String, Obj> = HashMap::new();
        let mut normalized_params: Vec<ParamGroupWithParamType> = Vec::new();
        let mut param_index: usize = 0;

        for param_def_with_type in exist_fact.params_def_with_type().groups.iter() {
            let mut new_param_names: Vec<String> = Vec::new();
            for original_name in param_def_with_type.params.iter() {
                let normalized_name = format!("#{}", param_index);
                param_index += 1;

                param_to_arg_map.insert(
                    original_name.clone(),
                    obj_for_bound_param_in_scope(normalized_name.clone(), ParamObjType::Exist),
                );
                new_param_names.push(normalized_name);
            }

            let instantiated_param_type = runtime.inst_param_type(
                &param_def_with_type.param_type,
                &param_to_arg_map,
                ParamObjType::Exist,
            )?;
            normalized_params.push(ParamGroupWithParamType::new(
                new_param_names,
                instantiated_param_type,
            ));
        }

        let instantiated_exist_fact =
            runtime.inst_exist_fact(exist_fact, &param_to_arg_map, ParamObjType::Exist, None)?;

        let mut fact_strings: Vec<String> = Vec::new();
        for fact in instantiated_exist_fact.facts().iter() {
            let fact_as_fact = fact.from_ref_to_cloned_fact();
            fact_strings.push(fact_as_fact.to_string());
        }

        let mut params_string_parts: Vec<String> = Vec::new();
        for param_def_with_type in normalized_params.iter() {
            params_string_parts.push(format!(
                "{} {}",
                param_def_with_type.params.join(","),
                param_def_with_type.param_type
            ));
        }
        let params_string = params_string_parts.join("; ");
        let facts_string = fact_strings.join("; ");
        Ok(format!("{} || {}", params_string, facts_string))
    }
}

fn stmt_result_infers(result: &StmtResult) -> InferResult {
    result.infer_result()
}
