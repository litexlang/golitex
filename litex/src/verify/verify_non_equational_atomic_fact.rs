use crate::fact::AtomicFact;
use crate::result::StmtResult;
use crate::error::{VerifyFactError};
use crate::execute::Executor;
use crate::verify::VerifyState;
use crate::result::StmtUnknown;

impl<'a> Executor<'a> {
    pub fn verify_non_equational_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        let mut result = self.verify_non_equational_atomic_fact_with_builtin_rules(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        result = self.verify_non_equational_atomic_fact_with_known_atomic_fact(atomic_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(StmtResult::StmtUnknown(StmtUnknown::new()))
    }
    
    pub fn verify_non_equational_atomic_fact_with_known_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        if atomic_fact.number_of_args() == 1 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(atomic_fact, verify_state)
        } else if atomic_fact.number_of_args() == 2 {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(atomic_fact, verify_state)
        } else {
            self.verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(atomic_fact, verify_state)
        }
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_1_param(&mut self, _atomic_fact: &AtomicFact, _verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        // TODO: iterate environments and check if known_atomic_facts_with_1_arg contains this atomic_fact
        Ok(StmtResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_2_params(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        panic!("not implemented");
    }

    fn verify_atomic_fact_not_equality_with_known_atomic_fact_with_0_or_more_than_2_params(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        panic!("not implemented");
    }

    fn verify_non_equational_atomic_fact_with_builtin_rules(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<StmtResult, VerifyFactError> {
        match atomic_fact {
            AtomicFact::InFact(in_fact) => self.verify_in_fact_with_builtin_rules(in_fact, verify_state),
            _ => Ok(StmtResult::StmtUnknown(StmtUnknown::new())),
        }
    }
}