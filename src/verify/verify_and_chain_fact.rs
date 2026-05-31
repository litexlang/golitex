use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&and_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            let well_defined_state = verify_state.without_known_forall_for_equality();
            if let Err(e) = self.verify_and_fact_well_defined(and_fact, &well_defined_state) {
                return Err(RuntimeError::from(VerifyRuntimeError(
                    RuntimeErrorStruct::new(
                        Some(Fact::from(and_fact.clone()).into_stmt()),
                        String::new(),
                        and_fact.line_file(),
                        Some(e),
                        vec![],
                    ),
                )));
            }
        }

        if let Some(fact_verified) =
            self.try_verify_and_fact_with_known_forall_facts_in_envs(and_fact, verify_state)?
        {
            return Ok(fact_verified.into());
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let mut child_results: Vec<StmtResult> = Vec::with_capacity(and_fact.facts.len());
        for fact in &and_fact.facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result);
            }
            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            and_fact.clone().into(),
            VerifiedByResult::wrap_bys(vec![VerifiedBysEnum::fact_with_note(
                and_fact.clone().into(),
                Some("and: each conjunct verified in order".to_string()),
            )]),
            child_results,
        ))
        .into())
    }

    fn try_verify_and_fact_with_known_forall_facts_in_envs(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<Option<FactualStmtSuccess>, RuntimeError> {
        let key = and_fact.key();
        let envs_count = self.environment_stack.len();
        for i in 0..envs_count {
            let stack_idx = envs_count - 1 - i;
            let known_forall_facts_count = {
                let env = &self.environment_stack[stack_idx];
                match env.known_and_facts_in_forall_facts.get(&key) {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            for j in 0..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let (and_fact_in_known_forall, current_known_forall) = {
                    let env = &self.environment_stack[stack_idx];
                    let Some(known_forall_facts_in_env) =
                        env.known_and_facts_in_forall_facts.get(&key)
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    current_known_forall.clone()
                };
                let match_result = self.match_args_in_fact_in_known_forall_fact_with_given_args(
                    &and_fact_in_known_forall.get_args_from_fact_ref(),
                    &and_fact.get_args_from_fact_ref(),
                )?;
                if let Some(arg_map) = match_result {
                    if let Some(fact_verified) = self
                        .verify_and_fact_args_satisfy_forall_requirements(
                            &and_fact_in_known_forall,
                            &current_known_forall,
                            arg_map,
                            and_fact,
                            verify_state,
                        )?
                    {
                        return Ok(Some(fact_verified));
                    }
                }
            }
        }
        Ok(None)
    }

    fn verify_and_fact_args_satisfy_forall_requirements(
        &mut self,
        and_fact_in_known_forall: &AndFact,
        known_forall: &Rc<KnownForallFactParamsAndDom>,
        arg_map: HashMap<String, Obj>,
        given_and_fact: &AndFact,
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
                RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                    Some(Fact::from(given_and_fact.clone()).into_stmt()),
                    String::new(),
                    given_and_fact.line_file(),
                    Some(e),
                    vec![],
                )))
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
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(given_and_fact.clone()).into_stmt()),
                        String::new(),
                        given_and_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                })?;
            let result = self
                .verify_fact(&instantiated_dom_fact, verify_state)
                .map_err(|e| {
                    RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(given_and_fact.clone()).into_stmt()),
                        String::new(),
                        given_and_fact.line_file(),
                        Some(e),
                        vec![],
                    )))
                })?;
            if result.is_unknown() {
                return Ok(None);
            }
        }

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![and_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_and_fact.clone().into(),
            VerifiedByResult::cited_fact(
                given_and_fact.clone().into(),
                verified_by_known_forall_fact.into(),
                None,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    pub fn verify_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&chain_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            let well_defined_state = verify_state.without_known_forall_for_equality();
            if let Err(e) = self.verify_chain_fact_well_defined(chain_fact, &well_defined_state) {
                return Err(RuntimeError::from(VerifyRuntimeError(
                    RuntimeErrorStruct::new(
                        Some(Fact::from(chain_fact.clone()).into_stmt()),
                        String::new(),
                        chain_fact.line_file(),
                        Some(e),
                        vec![],
                    ),
                )));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        let facts = chain_fact.facts().map_err(|e| {
            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::ChainFact(chain_fact.clone()).into_stmt()),
                String::new(),
                chain_fact.line_file(),
                Some(e),
                vec![],
            )))
        })?;
        let mut child_results: Vec<StmtResult> = Vec::with_capacity(facts.len());
        for fact in &facts {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok((StmtUnknown::new_with_detail(format!(
                    "unverified chain step: {}",
                    fact
                )))
                .into());
            }

            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            chain_fact.clone().into(),
            VerifiedByResult::wrap_bys(vec![VerifiedBysEnum::fact_with_note(
                chain_fact.clone().into(),
                Some("chain: each step verified in order".to_string()),
            )]),
            child_results,
        ))
        .into())
    }
}
