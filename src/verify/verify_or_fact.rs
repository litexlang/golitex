use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(cached_result) =
            self.verify_fact_from_cache_using_display_string(&or_fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_or_fact_well_defined(or_fact, verify_state) {
                return Err(
                    RuntimeError::new_verify_error_with_fact_msg_position_previous_error(
                        or_fact.clone().into(),
                        String::new(),
                        or_fact.line_file.clone(),
                        Some(e),
                    ),
                );
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        if or_fact.facts.len() == 2 {
            if let (
                AndChainAtomicFact::AtomicFact(first_atomic),
                AndChainAtomicFact::AtomicFact(second_atomic),
            ) = (&or_fact.facts[0], &or_fact.facts[1])
            {
                if first_atomic.make_reversed().to_string() == second_atomic.to_string() {
                    return Ok((FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            or_fact.clone().into(),
                            "or: complementary atomic facts (make_reversed first equals second)"
                                .to_string(),
                            Vec::new(),
                        )).into());
                }
            }
        }

        for fact in or_fact.facts.iter() {
            let result = self.verify_and_chain_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_true() {
                return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                        or_fact.clone().into(),
                        fact.to_string(),
                        None,
                        Some(fact.line_file()),
                        Vec::new(),
                    )).into());
            }
        }

        let result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        let result = self.verify_or_fact_with_known_forall(or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_or_fact_with_known_or_facts(
        &mut self,
        or_fact: &OrFact,
    ) -> Result<StmtResult, RuntimeError> {
        let args_in_or_fact = or_fact.get_args_from_fact();
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in args_in_or_fact.iter() {
            let mut all_objs_equal_to_current_arg =
                self.get_all_objs_equal_to_given(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
        }

        for environment in self.iter_environments_from_top() {
            let result = Self::verify_or_fact_with_known_or_facts_with_facts_in_environment(
                environment,
                or_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        Ok((StmtUnknown::new()).into())
    }

    pub fn verify_or_fact_with_known_or_facts_with_facts_in_environment(
        environment: &Environment,
        or_fact: &OrFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<StmtResult, RuntimeError> {
        if let Some(known_or_facts) = environment.known_or_facts.get(&or_fact.key()) {
            for known_or_fact in known_or_facts.iter() {
                let result = Self::_verify_or_fact_the_same_type_and_return_matched_args(
                    known_or_fact,
                    or_fact,
                )?;
                let mut all_args_match = true;
                if let Some(matched_args) = result {
                    for (index, matched_arg) in matched_args.iter().enumerate() {
                        let known_arg_string = matched_arg.0.to_string();

                        if known_arg_string != matched_arg.1.to_string()
                            && !all_objs_equal_to_each_arg[index].contains(&known_arg_string)
                        {
                            all_args_match = false;
                            break;
                        }
                    }
                }

                if all_args_match {
                    return Ok((FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                            or_fact.clone().into(),
                            known_or_fact.to_string(),
                            Some(known_or_fact.clone().into()),
                            None,
                            Vec::new(),
                        )).into());
                }
            }
        }

        return Ok((StmtUnknown::new()).into());
    }
}
