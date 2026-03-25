use crate::environment::Environment;
use crate::error::{RuntimeError, VerifyError};
use crate::execute::Runtime;
use crate::fact::{Fact, OrFact};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult, StmtUnknown};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Runtime<'a> {
    pub fn verify_or_fact(
        &mut self,
        or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let fact_display_string = or_fact.to_string();
        let fact_line_file = or_fact.line_file;
        if let Some(cached_result) = self.verify_fact_from_cache_using_display_string(
            &Fact::OrFact(or_fact.clone()),
        ) {
            return Ok(cached_result);
        }

        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_or_fact_well_defined(or_fact, verify_state) {
                return Err(VerifyError::new(
                    fact_display_string,
                    Some(RuntimeError::WellDefinedError(e)),
                    fact_line_file,
                ));
            }
        }

        let verify_state_for_children = verify_state.make_state_with_req_ok_set_to_true();

        for fact in or_fact.facts.iter() {
            let result = self.verify_and_chain_atomic_fact(fact, &verify_state_for_children)?;
            if result.is_true() {
                return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                    FactVerifiedByFact::new(
                        Fact::OrFact(or_fact.clone()),
                        fact.to_string(),
                        InferResult::new(),
                        fact.line_file(),
                    ),
                ));
            }
        }

        let mut result = self.verify_or_fact_with_known_or_facts(or_fact)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_or_fact_with_known_forall(or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_or_fact_with_known_or_facts(
        &mut self,
        or_fact: &OrFact,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let args_in_or_fact = or_fact.get_args_from_fact();
        let mut all_objs_equal_to_each_arg: Vec<Vec<String>> = Vec::new();
        for arg in args_in_or_fact.iter() {
            let mut all_objs_equal_to_current_arg = self
                .runtime_context
                .get_all_objs_equal_to_arg(&arg.to_string());
            if all_objs_equal_to_current_arg.is_empty() {
                all_objs_equal_to_current_arg.push(arg.to_string());
            }
            all_objs_equal_to_each_arg.push(all_objs_equal_to_current_arg);
        }

        for environment in self.runtime_context.iter_environments_from_top() {
            let result = Self::verify_or_fact_with_known_or_facts_with_facts_in_environment(
                environment,
                or_fact,
                &all_objs_equal_to_each_arg,
            )?;
            if result.is_true() {
                return Ok(result);
            }
        }

        let result = Self::verify_or_fact_with_known_or_facts_with_facts_in_environment(
            &self.runtime_context.builtin_environment,
            or_fact,
            &all_objs_equal_to_each_arg,
        )?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    pub fn verify_or_fact_with_known_or_facts_with_facts_in_environment(
        environment: &Environment,
        or_fact: &OrFact,
        all_objs_equal_to_each_arg: &Vec<Vec<String>>,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
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
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(
                        FactVerifiedByFact::new(
                            Fact::OrFact(or_fact.clone()),
                            known_or_fact.to_string(),
                            InferResult::new(),
                            known_or_fact.line_file,
                        ),
                    ));
                }
            }
        }

        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
    }
}
