use crate::fact::AtomicFact;
use crate::environment::Environment;
use crate::result::{FactVerifiedByFact, NonErrStmtResult};
use crate::error::{VerifyError};
use crate::execute::Executor;
use crate::verify::VerifyState;
use crate::result::StmtUnknown;

impl<'a> Executor<'a> {
    pub fn verify_non_equational_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        let mut result = self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_fact(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
    }
    
    pub fn verify_non_equational_atomic_fact_with_known_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact, verify_state)
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact, verify_state)
        } else {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(atomic_fact, verify_state)
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(&mut self, atomic_fact: &AtomicFact, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        let all_objs_equal_to_arg = self.runtime_context.get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());
        
        for environment in self.runtime_context.environments.iter() {
            let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment, atomic_fact, &all_objs_equal_to_arg, _verify_state)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        let result = Self::verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(&self.runtime_context.builtin_environment, atomic_fact, &all_objs_equal_to_arg, _verify_state)?;
        if result.is_true() {
            return Ok(result);
        }
        
        Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(&mut self, atomic_fact: &AtomicFact, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        let all_objs_equal_to_arg0 = self.runtime_context.get_all_objs_equal_to_arg(&atomic_fact.args()[0].to_string());
        let all_objs_equal_to_arg1 = self.runtime_context.get_all_objs_equal_to_arg(&atomic_fact.args()[1].to_string());
        
        for environment in self.runtime_context.environments.iter() {
            if let Some(known_facts_map) = environment.known_atomic_facts_with_2_args.get(&(atomic_fact.key(), atomic_fact.is_true())) {
                if known_facts_map.contains_key(&(atomic_fact.args()[0].to_string(), atomic_fact.args()[1].to_string())) {
                    return Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(atomic_fact.to_string(), "known atomic fact".to_string(), atomic_fact.line_file_index())));
                }
            }
        }
        
        if let Some(known_facts_map) = self.runtime_context.builtin_environment.known_atomic_facts_with_2_args.get(&(atomic_fact.key(), atomic_fact.is_true())) {
            if known_facts_map.contains_key(&(atomic_fact.args()[0].to_string(), atomic_fact.args()[1].to_string())) {
                return Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(atomic_fact.to_string(), "known atomic fact".to_string(), atomic_fact.line_file_index())));
            }
        }
        
        Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(&mut self, _atomic_fact: &AtomicFact, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        panic!("not implemented");
    }

    fn verify_non_equational_atomic_fact_with_builtin_rules(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        match atomic_fact {
            AtomicFact::InFact(in_fact) => self.verify_in_fact_with_builtin_rules(in_fact, verify_state),
            _ => Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param_with_facts_in_environment(environment: &Environment, atomic_fact: &AtomicFact, all_objs_equal_to: &Vec<String>, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        if let Some(known_facts_map) = environment.known_atomic_facts_with_1_arg.get(&(atomic_fact.key(), atomic_fact.is_true())) {
            for obj in all_objs_equal_to.iter() {
                if known_facts_map.contains_key(obj) {
                    return Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(atomic_fact.to_string(), "known atomic fact".to_string(), atomic_fact.line_file_index())));
                }
            }
        }

        Ok(NonErrStmtResult::StmtUnknown(StmtUnknown::new()))
    }
}