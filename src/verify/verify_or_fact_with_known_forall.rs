use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

// Same ∀-instantiation strategy as `verify_atomic_fact_with_known_forall` (σ from template to given).

impl Runtime {
    pub fn verify_or_fact_with_known_forall(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(fact_verified) =
            self.try_verify_or_fact_with_known_forall_facts_in_envs(or_fact, verify_state)?
        {
            return Ok((fact_verified).into());
        }
        Ok((StmtUnknown::new()).into())
    }

    fn get_matched_or_fact_in_known_forall_fact_in_envs(
        &mut self,
        iterate_from_env_index: usize,
        iterate_from_known_forall_fact_index: usize,
        given_or_fact: &OrFact,
    ) -> Result<
        (
            (usize, usize),
            Option<HashMap<String, Obj>>,
            Option<(OrFact, Rc<KnownForallFactParamsAndDom>)>,
        ),
        RuntimeError,
    > {
        let lookup_key = given_or_fact.key();

        let envs_count = self.environment_stack.len();
        for i in iterate_from_env_index..envs_count {
            let stack_idx = envs_count - 1 - i;
            let known_forall_facts_count = {
                let env = &self.environment_stack[stack_idx];
                match env.known_or_facts_in_forall_facts.get(lookup_key.as_str()) {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            for j in iterate_from_known_forall_fact_index..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let (fact_args_in_known_forall, given_fact_args, current_known_forall) = {
                    let env = &self.environment_stack[stack_idx];
                    let Some(known_forall_facts_in_env) =
                        env.known_or_facts_in_forall_facts.get(lookup_key.as_str())
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    (
                        current_known_forall.0.get_args_from_fact(),
                        given_or_fact.get_args_from_fact(),
                        current_known_forall.clone(),
                    )
                };
                let match_result = self.match_args_in_fact_in_known_forall_fact_with_given_args(
                    &fact_args_in_known_forall,
                    &given_fact_args,
                )?;
                if let Some(arg_map) = match_result {
                    return Ok(((i, j), Some(arg_map), Some(current_known_forall)));
                }
            }
        }

        Ok(((0, 0), None, None))
    }

    fn try_verify_or_fact_with_known_forall_facts_in_envs(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let mut iterate_from_env_index = 0;
        let mut iterate_from_known_forall_fact_index = 0;

        loop {
            let result = self.get_matched_or_fact_in_known_forall_fact_in_envs(
                iterate_from_env_index,
                iterate_from_known_forall_fact_index,
                or_fact,
            )?;
            let ((i, j), arg_map_opt, known_forall_opt) = result;
            match (arg_map_opt, known_forall_opt) {
                (Some(arg_map), Some((or_fact_in_known_forall, forall_rc))) => {
                    if let Some(fact_verified) = self
                        .verify_or_fact_args_satisfy_forall_requirements(
                            &or_fact_in_known_forall,
                            &forall_rc,
                            arg_map,
                            or_fact,
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

    fn verify_or_fact_args_satisfy_forall_requirements(
        &mut self,
        or_fact_in_known_forall: &OrFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
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
                        Some(Fact::from(given_or_fact.clone()).into_stmt()),
                        String::new(),
                        given_or_fact.line_file.clone(),
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
                            Some(Fact::from(given_or_fact.clone()).into_stmt()),
                            String::new(),
                            given_or_fact.line_file.clone(),
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
                            Some(Fact::from(given_or_fact.clone()).into_stmt()),
                            String::new(),
                            given_or_fact.line_file.clone(),
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
            vec![or_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_or_fact.clone().into(),
            VerifiedByResult::wrap_bys(vec![VerifiedByResult::Fact(
                verified_by_known_forall_fact.clone().into(),
                verified_by_known_forall_fact.to_string(),
            )]),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }
}
