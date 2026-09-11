//! Verification for conjunctions and ordered relation chains.

use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;
use std::result::Result;

impl Runtime {
    pub(in crate::verification) fn prove_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&and_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if let Some(fact_verified) =
            self.try_verify_and_fact_with_known_forall_facts_in_envs(and_fact, verify_state)?
        {
            return Ok(fact_verified.into());
        }

        let verify_state_for_children = verify_state.clone();

        let mut child_results: Vec<VerifyFactResult> = Vec::with_capacity(and_fact.facts.len());
        for fact in and_fact.facts.iter() {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(result
                    .as_fact_unknown()
                    .cloned()
                    .expect("unknown atomic verification carries an atomic unknown")
                    .into());
            }
            child_results.push(result);
        }
        Ok((SuccessProveFactResult::new_with_verified_by_known_fact(
            and_fact.clone().into(),
            SuccessFactProofResult::combined_steps(Vec::new()),
            child_results,
        ))
        .into())
    }

    fn try_verify_and_fact_with_known_forall_facts_in_envs(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
        let key = and_fact.key();
        let envs_count = self.environment_count();
        for stack_idx in 0..envs_count {
            let known_forall_facts_count = {
                let env = self
                    .environment_by_top_index(stack_idx)
                    .expect("environment index should be valid");
                match env.facts.forall_conclusions.conjunction.get(&key) {
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
                        env.facts.forall_conclusions.conjunction.get(&key)
                    else {
                        continue;
                    };
                    let Some(current_known_forall) = known_forall_facts_in_env.get(entry_idx)
                    else {
                        continue;
                    };
                    current_known_forall.clone()
                };
                let match_result = self.match_args_in_fact_with_known_forall_bindings(
                    &and_fact_in_known_forall.get_args_from_fact_ref(),
                    &and_fact.get_args_from_fact_ref(),
                    &current_known_forall.params_def,
                    None,
                )?;
                if let Some((arg_map, _)) = match_result {
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
        _and_fact_in_known_forall: &AndFact,
        known_forall: &Rc<StoredForallConclusionReference>,
        arg_map: HashMap<String, Obj>,
        given_and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<Option<SuccessProveFactResult>, RuntimeError> {
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

        let source_fact = known_forall.source_fact();
        let source_fact_id = known_forall.source_fact_id;
        let fact_verified = SuccessProveFactResult::new_with_verified_by_known_fact(
            given_and_fact.clone().into(),
            SuccessFactProofResult::known_forall_instantiation(
                source_fact,
                source_fact_id,
                known_forall.conclusion_location,
                instantiation,
                requirements,
            ),
            Vec::new(),
        );
        Ok(Some(fact_verified))
    }

    pub(in crate::verification) fn prove_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&chain_fact.clone().into())
        {
            return Ok(cached_result);
        }

        let verify_state_for_children = verify_state.clone();

        let facts = chain_fact.facts(self).map_err(|e| {
            RuntimeError::from(VerifyRuntimeError(RuntimeErrorStruct::new(
                Some(Fact::ChainFact(chain_fact.clone()).into_stmt()),
                String::new(),
                chain_fact.line_file(),
                Some(e),
                vec![],
            )))
        })?;
        let mut child_results: Vec<VerifyFactResult> = Vec::with_capacity(facts.len());
        for fact in facts.iter() {
            let result = self.verify_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_unknown() {
                return Ok(UnknownGenericStmtResult::new_with_detail(format!(
                    "unverified chain step: {}",
                    fact
                ))
                .into());
            }

            child_results.push(result);
        }
        Ok((SuccessProveFactResult::new_with_verified_by_known_fact(
            chain_fact.clone().into(),
            SuccessFactProofResult::combined_steps(Vec::new()),
            child_results,
        ))
        .into())
    }
}
