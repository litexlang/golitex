use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub fn verify_exist_fact_with_known_forall(
        &mut self,
        exist_fact: &ExistFact,
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
        &self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_exist_fact: &ExistFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(ExistFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let lookup_key = given_exist_fact.key();

        let envs_count = self.environment_stack.len();
        for i in iterate_from_env_index..envs_count {
            let env = &self.environment_stack[envs_count - 1 - i];
            if let Some(known_forall_facts_in_env) = env
                .known_exist_facts_in_forall_facts
                .get(lookup_key.as_str())
            {
                let known_forall_facts_count = known_forall_facts_in_env.len();
                for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                    let current_known_forall =
                        &known_forall_facts_in_env[known_forall_facts_count - 1 - j];
                    let fact_args_in_known_forall = current_known_forall.0.get_args_from_fact();
                    let given_fact_args = given_exist_fact.get_args_from_fact();
                    let match_result =
                        Self::match_args_in_fact_in_known_forall_fact_with_given_args(
                            &fact_args_in_known_forall,
                            &given_fact_args,
                        )?;
                    if let Some(arg_map) = match_result {
                        return Ok(((i, j), Some(arg_map), Some(current_known_forall.clone())));
                    }
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_exist_fact_with_known_forall_facts_in_envs(
        &mut self,
        exist_fact: &ExistFact,
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
        exist_fact_in_known_forall: &ExistFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_exist_fact: &ExistFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        // exist param matches exist param
        let given_exist_param_names =
            ParamGroupWithParamType::collect_param_names(&given_exist_fact.params_def_with_type);

        let known_exist_param_names = ParamGroupWithParamType::collect_param_names(
            &exist_fact_in_known_forall.params_def_with_type,
        );
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
                    if v.to_string() != given_param_name.to_string() {
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
            if given_exist_param_names.contains(&obj.to_string()) {
                if !known_exist_param_names.contains(key) {
                    return Ok(None);
                }
            }
        }

        // arg that matches forall params
        let param_names = ParamGroupWithParamType::collect_param_names(&known_forall.params_def);

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

        for (key, obj) in arg_map.iter() {
            if param_names.contains(key) || known_exist_param_names.contains(key) {
                continue;
            } else {
                if key != &obj.to_string() {
                    return Ok(None);
                }
            }
        }

        let _: InferResult = self
            .verify_args_satisfy_param_def_flat_types(
                &known_forall.params_def,
                &args_for_params,
                verify_state,
            )
            .map_err(|e| {
                RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                    given_exist_fact.clone().into(),
                    String::new(),
                    given_exist_fact.line_file(),
                    Some(e),
                )
            })?;

        let param_to_arg_map = match ParamGroupWithParamType::param_def_params_to_arg_map(
            &known_forall.params_def,
            &arg_map,
        ) {
            Some(m) => m,
            None => return Ok(None),
        };

        for dom_fact in known_forall.dom.iter() {
            let instantiated_dom_fact = self
                .inst_exist_or_and_chain_atomic_fact(dom_fact, &param_to_arg_map)
                .map_err(|e| {
                    RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                        given_exist_fact.clone().into(),
                        String::new(),
                        given_exist_fact.line_file(),
                        Some(e),
                    )
                })?;
            let result =
                self.verify_exist_or_and_chain_atomic_fact(&instantiated_dom_fact, verify_state)?;
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
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
            given_exist_fact.clone().into(),
            verified_by_known_forall_fact.to_string(),
            Some(verified_by_known_forall_fact.clone().into()),
            None,
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }
}
