use crate::prelude::*;
use std::collections::HashMap;
use std::result::Result;

impl Runtime {
    pub fn verify_exist_fact(
        &mut self,
        exist_fact: &ExistFact,
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

            if exist_fact.is_exist_unique {
                if let Some(proved) = self.try_verify_exist_unique_by_exist_and_uniqueness_forall(
                    exist_fact,
                    verify_state,
                )? {
                    return Ok(proved);
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub(crate) fn build_exist_unique_uniqueness_forall_fact(
        &self,
        exist_fact: &ExistFact,
    ) -> Result<ForallFact, RuntimeError> {
        let lf = exist_fact.line_file();
        let n = exist_fact.params_def_with_type.number_of_params();
        let flat_orig = exist_fact.params_def_with_type.collect_param_names();
        let flat_all = self.generate_random_unused_names(2 * n);
        let flat_a: Vec<String> = flat_all[..n].to_vec();
        let flat_b: Vec<String> = flat_all[n..2 * n].to_vec();

        let mut map_running_a: HashMap<String, Obj> = HashMap::new();
        let mut map_running_b: HashMap<String, Obj> = HashMap::new();
        let mut forall_groups: Vec<ParamGroupWithParamType> = Vec::new();
        let mut idx: usize = 0;
        for group in exist_fact.params_def_with_type.groups.iter() {
            let len = group.params.len();
            let chunk_a = flat_a[idx..idx + len].to_vec();
            for (orig, nm) in group.params.iter().zip(chunk_a.iter()) {
                map_running_a.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Exist),
                );
            }
            let pt_a = self.inst_param_type(&group.param_type, &map_running_a, ParamObjType::Exist)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_a, pt_a));
            idx += len;
        }
        idx = 0;
        for group in exist_fact.params_def_with_type.groups.iter() {
            let len = group.params.len();
            let chunk_b = flat_b[idx..idx + len].to_vec();
            for (orig, nm) in group.params.iter().zip(chunk_b.iter()) {
                map_running_b.insert(
                    orig.clone(),
                    obj_for_bound_param_in_scope(nm.clone(), ParamObjType::Exist),
                );
            }
            let pt_b = self.inst_param_type(&group.param_type, &map_running_b, ParamObjType::Exist)?;
            forall_groups.push(ParamGroupWithParamType::new(chunk_b, pt_b));
            idx += len;
        }

        let map_a: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_a
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Exist)),
            )
            .collect();
        let map_b: HashMap<String, Obj> = flat_orig
            .iter()
            .cloned()
            .zip(
                flat_b
                    .iter()
                    .cloned()
                    .map(|s| obj_for_bound_param_in_scope(s, ParamObjType::Exist)),
            )
            .collect();

        let mut dom_facts: Vec<Fact> = Vec::new();
        for inner in exist_fact.facts.iter() {
            let f_a = self.inst_or_and_chain_atomic_fact(inner, &map_a, ParamObjType::Exist)?;
            let o: OrAndChainAtomicFact = f_a;
            dom_facts.push(o.into());
        }
        for inner in exist_fact.facts.iter() {
            let f_b = self.inst_or_and_chain_atomic_fact(inner, &map_b, ParamObjType::Exist)?;
            let o: OrAndChainAtomicFact = f_b;
            dom_facts.push(o.into());
        }

        let mut then_facts: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        if n == 1 {
            let eq = EqualFact::new(
                obj_for_bound_param_in_scope(flat_a[0].clone(), ParamObjType::Forall),
                obj_for_bound_param_in_scope(flat_b[0].clone(), ParamObjType::Forall),
                lf.clone(),
            );
            then_facts.push(ExistOrAndChainAtomicFact::AtomicFact(eq.into()));
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

        Ok(ForallFact::new(
            ParamDefWithType::new(forall_groups),
            dom_facts,
            then_facts,
            lf,
        ))
    }

    fn try_verify_exist_unique_by_exist_and_uniqueness_forall(
        &mut self,
        exist_fact: &ExistFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        if exist_fact.params_def_with_type.number_of_params() == 0 {
            return Ok(None);
        }
        let plain = ExistFact::new(
            exist_fact.params_def_with_type.clone(),
            exist_fact.facts.clone(),
            false,
            exist_fact.line_file.clone(),
        );
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

        let out = FactualStmtSuccess::new_with_verified_by_known_fact_source(
            exist_fact.clone().into(),
            infers,
            "exist_unique: witness exist and uniqueness forall verified".to_string(),
            Some(uniqueness_fact),
            None,
            vec![],
        );
        Ok(Some(out.into()))
    }

    pub fn verify_exist_fact_with_known_exist_fact(
        &mut self,
        exist_fact: &ExistFact,
        known_exist_fact: &ExistFact,
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
        exist_fact: &ExistFact,
        known_exist_fact: &ExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        if exist_fact.is_exist_unique != known_exist_fact.is_exist_unique {
            return Ok((StmtUnknown::new()).into());
        }
        if let Some(known_exist_facts) = environment.known_exist_facts.get(&known_exist_fact.key())
        {
            let target_string =
                Self::exist_fact_normalized_string(runtime, exist_fact).map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(exist_fact.clone()).into_stmt()),
                            String::new(),
                            exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            for known_fact in known_exist_facts.iter() {
                if known_fact.is_exist_unique != exist_fact.is_exist_unique {
                    continue;
                }
                let known_string = Self::exist_fact_normalized_string(runtime, known_fact)
                    .map_err(|e| {
                        {
                            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                                Some(Fact::from(exist_fact.clone()).into_stmt()),
                                String::new(),
                                exist_fact.line_file(),
                                Some(e),
                                vec![],
                            )))
                        }
                    })?;
                if target_string == known_string {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                            exist_fact.clone().into(),
                            known_fact.to_string(),
                            Some(known_fact.clone().into()),
                            None,
                            Vec::new(),
                        )).into());
                }
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    fn exist_fact_normalized_string(
        runtime: &Runtime,
        exist_fact: &ExistFact,
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

            let instantiated_param_type =
                runtime.inst_param_type(&param_def_with_type.param_type, &param_to_arg_map, ParamObjType::Exist)?;
            normalized_params.push(ParamGroupWithParamType::new(
                new_param_names,
                instantiated_param_type,
            ));
        }

        let instantiated_exist_fact = runtime.inst_exist_fact(exist_fact, &param_to_arg_map, ParamObjType::Exist)?;

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
        let head = if exist_fact.is_exist_unique {
            EXIST_UNIQUE
        } else {
            EXIST
        };

        Ok(format!("{} || {} || {}", head, params_string, facts_string))
    }
}

fn stmt_result_infers(result: &StmtResult) -> InferResult {
    match result {
        StmtResult::FactualStmtSuccess(x) => x.infers.clone(),
        StmtResult::NonFactualStmtSuccess(x) => x.infers.clone(),
        StmtResult::StmtUnknown(_) => InferResult::new(),
    }
}
