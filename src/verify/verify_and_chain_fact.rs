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

        let verify_state_for_children = verify_state.with_well_defined_already_verified();

        let mut child_results: Vec<StmtResult> = Vec::with_capacity(and_fact.facts.len());
        for fact in and_fact.facts.iter() {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result);
            }
            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            and_fact.clone().into(),
            VerifiedByResult::wrap_bys(Vec::new()),
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
        let envs_count = self.environment_count();
        for stack_idx in 0..envs_count {
            let known_forall_facts_count = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                match env.known_and_facts_in_forall_facts.get(&key) {
                    Some(v) => v.len(),
                    None => continue,
                }
            };
            for j in 0..known_forall_facts_count {
                let entry_idx = known_forall_facts_count - 1 - j;
                let (and_fact_in_known_forall, current_known_forall) = {
                    let env = self
                        .environment_by_top_index(stack_idx)
                        .expect("environment index should be valid");
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
        let Some((instantiation, requirements)) = self
            .verify_known_forall_requirements_and_build_evidence(
                known_forall.as_ref(),
                &arg_map,
                given_and_fact.clone().into(),
                verify_state,
            )?
        else {
            return Ok(None);
        };

        let verified_by_known_forall_fact = ForallFact::new(
            known_forall.params_def.clone(),
            known_forall.dom.clone(),
            vec![and_fact_in_known_forall.clone().into()],
            known_forall.line_file.clone(),
        )?;
        let fact_verified = FactualStmtSuccess::new_with_verified_by_known_fact(
            given_and_fact.clone().into(),
            VerifiedByResult::known_forall_instantiation(
                verified_by_known_forall_fact.into(),
                instantiation,
                requirements,
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

        let verify_state_for_children = verify_state.with_well_defined_already_verified();

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
        for fact in facts.iter() {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(StmtUnknown::new_with_detail(format!(
                    "unverified chain step: {}",
                    fact
                ))
                .into());
            }

            child_results.push(result);
        }
        Ok((FactualStmtSuccess::new_with_verified_by_known_fact(
            chain_fact.clone().into(),
            VerifiedByResult::wrap_bys(Vec::new()),
            child_results,
        ))
        .into())
    }
}
