use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

// Same ∀-instantiation strategy as `verify_atomic_fact_with_known_forall`, plus exist-internal params.

impl Runtime {
    pub fn verify_exist_fact_with_known_forall(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_exist_fact_with_known_forall_facts_in_envs(exist_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }
        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_exist_fact_in_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_exist_fact: &ExistFactEnum,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let lookup_keys = known_exist_lookup_keys_for_forall_bucket(given_exist_fact);

        let envs_count = self.environment_stack.len();
        for i in iterate_from_env_index..envs_count {
            let env = &self.environment_stack[envs_count - 1 - i];
            let mut merged_bucket: Vec<(ExistFactEnum, Rc<KnownForallFactParamsAndDom>)> =
                Vec::new();
            for lk in lookup_keys.iter() {
                if let Some(known_forall_facts_in_env) =
                    env.known_exist_facts_in_forall_facts.get(lk.as_str())
                {
                    merged_bucket.extend(known_forall_facts_in_env.iter().cloned());
                }
            }
            merged_bucket.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
            merged_bucket.dedup_by(|a, b| a.0.to_string() == b.0.to_string());
            if !merged_bucket.is_empty() {
                let known_forall_facts_count = merged_bucket.len();
                for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                    let entry_idx = known_forall_facts_count - 1 - j;
                    let (fact_args_in_known_forall, given_fact_args, current_known_forall) = {
                        let current_known_forall = &merged_bucket[entry_idx];
                        (
                            current_known_forall.0.get_args_from_fact(),
                            given_exist_fact.get_args_from_fact(),
                            current_known_forall.clone(),
                        )
                    };
                    let match_result = self
                        .match_args_in_fact_in_known_forall_fact_with_given_args(
                            &fact_args_in_known_forall,
                            &given_fact_args,
                        )?;
                    if let Some(arg_map) = match_result {
                        let exist_in_forall = &current_known_forall.0;
                        if !exist_in_forall.can_be_used_to_verify_goal(given_exist_fact) {
                            continue;
                        }
                        return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                    }
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_exist_fact_with_known_forall_facts_in_envs(
        &mut self,
        exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_exist_fact_in_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                exist_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((exist_fact_in_known_forall, forall_rc))) => {
                    if let Some(fact_verified) = self
                        .verify_exist_fact_args_satisfy_forall_requirements(
                            &exist_fact_in_known_forall,
                            &forall_rc,
                            arg_map,
                            exist_fact,
                            verify_state,
                        )?
                    {
                        return Ok(Some(fact_verified));
                    }
                    iterate_from_env_index = i;
                    iterate_from_known_forall_fact_index = j + 1;
                }
                _ => return Ok(None),
            }
        }
    }

    fn verify_exist_fact_args_satisfy_forall_requirements(
        &mut self,
        exist_fact_in_known_forall: &ExistFactEnum,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_exist_fact: &ExistFactEnum,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        if !exist_fact_in_known_forall.can_be_used_to_verify_goal(given_exist_fact) {
            return Ok(None);
        }
        // exist param matches exist param
        let given_exist_param_names = given_exist_fact
            .params_def_with_type()
            .collect_param_names();

        let known_exist_param_names = exist_fact_in_known_forall
            .params_def_with_type()
            .collect_param_names();
        if !known_exist_param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        if given_exist_param_names.len() != known_exist_param_names.len() {
            return Ok(None);
        }

        let mut known_exist_params_to_given_exist_params_map: Vec<Obj> = Vec::new();
        for (known_param_name, given_param_name) in known_exist_param_names
            .iter()
            .zip(given_exist_param_names.iter())
        {
            let obj = match arg_map.get(known_param_name) {
                Some(v) => {
                    if !Self::obj_matches_exist_forall_binding_name(v, given_param_name) {
                        return Ok(None);
                    }
                    v
                }
                None => return Ok(None),
            };
            known_exist_params_to_given_exist_params_map.push(obj.clone());
        }

        // given exist param can only match known exist param, it can not match other params
        for (key, obj) in arg_map.iter() {
            if let Some(spine) = Self::obj_binding_spine_name_for_arg_map(obj) {
                if given_exist_param_names.iter().any(|n| n == spine) {
                    if !known_exist_param_names.contains(key) {
                        return Ok(None);
                    }
                }
            }
        }

        // arg that matches forall params
        let param_names = known_forall.params_def.collect_param_names();

        if !param_names
            .iter()
            .all(|param_name| arg_map.contains_key(param_name))
        {
            return Ok(None);
        }

        let mut args_for_params: Vec<Obj> = Vec::new();

        for param_name in param_names.iter() {
            let obj = match arg_map.get(param_name) {
                Some(v) => v,
                None => return Ok(None),
            };

            args_for_params.push(obj.clone());
        }

        let args_param_types = self
            .verify_args_satisfy_param_def_flat_types(
                &known_forall.params_def,
                &args_for_params,
                verify_state,
                ParamObjType::Forall,
            )
            .map_err(|e| {
                {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(given_exist_fact.clone()).into_stmt()),
                        String::new(),
                        given_exist_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                }
            })?;
        if args_param_types.is_unknown() {
            return Ok(None);
        }

        let param_to_arg_map = match known_forall
            .params_def
            .param_def_params_to_arg_map(&arg_map)
        {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = self
                .inst_fact(dom_fact, &param_to_arg_map, ParamObjType::Forall, None)
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(given_exist_fact.clone()).into_stmt()),
                            String::new(),
                            given_exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            let result = self
                .verify_fact(&instantiated_dom_fact, verify_state)
                .map_err(|e| {
                    {
                        RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                            Some(Fact::from(given_exist_fact.clone()).into_stmt()),
                            String::new(),
                            given_exist_fact.line_file(),
                            Some(e),
                            vec![],
                        )))
                    }
                })?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![exist_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        );
        let fact_verified =
            FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                given_exist_fact.clone().into(),
                verified_by_known_forall_fact.to_string(),
                Some(verified_by_known_forall_fact.clone().into()),
                None,
                Vec::new(),
            );
        Ok(Some(fact_verified))
    }

    fn obj_binding_spine_name_for_arg_map(obj: &Obj) -> Option<&str> {
        match obj {
            Obj::Atom(AtomObj::Exist(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Forall(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::FnSet(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Def(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::SetBuilder(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::Induc(p)) => Some(p.name.as_str()),
            Obj::Atom(AtomObj::DefAlgo(p)) => Some(p.name.as_str()),
            _ => None,
        }
    }

    fn obj_matches_exist_forall_binding_name(obj: &Obj, name: &str) -> bool {
        match obj {
            Obj::Atom(AtomObj::Exist(p)) => p.name == name,
            Obj::Atom(AtomObj::Forall(p)) => p.name == name,
            Obj::Atom(AtomObj::FnSet(p)) => p.name == name,
            Obj::Atom(AtomObj::Def(p)) => p.name == name,
            Obj::Atom(AtomObj::SetBuilder(p)) => p.name == name,
            Obj::Atom(AtomObj::Induc(p)) => p.name == name,
            Obj::Atom(AtomObj::DefAlgo(p)) => p.name == name,
            _ => obj.to_string() == name,
        }
    }
}

fn known_exist_lookup_keys_for_forall_bucket(goal: &ExistFactEnum) -> Vec<String> {
    let mut keys = vec![goal.alpha_normalized_key(), goal.key()];
    if let ExistFactEnum::ExistFact(body) = goal {
        let unique = ExistFactEnum::ExistUniqueFact(body.clone());
        keys.push(unique.alpha_normalized_key());
        keys.push(unique.key());
    }
    keys.sort();
    keys.dedup();
    keys
}
