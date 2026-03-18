use crate::environment::Environment;
use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::{AndChainAtomicFact, AtomicFact, OrFact};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult, StmtUnknown};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_or_fact(&mut self, or_fact: &OrFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        for fact in or_fact.facts.iter() {
            let result = self.verify_fact(&fact.to_fact(), verify_state)?;
            if result.is_true() {
                return Ok(NonErrStmtExecResult::FactVerifiedByFact(FactVerifiedByFact::new(
                    or_fact.to_string(),
                    fact.to_string(),
                    InferResult::new(),
                    or_fact.line_file_index,
                    or_fact.line_file_index,
                )));
            }
        }

        let result = self.verify_or_fact_with_known_or_facts(or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_or_fact_with_known_or_facts(&mut self, or_fact: &OrFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        for environment in self.runtime_context.iter_environments_from_top() {
            let result = Self::verify_or_fact_with_known_or_facts_in_environment(environment, or_fact, verify_state)?;
            if result.is_true() {
                return Ok(result);
            }
        }

        let result = Self::verify_or_fact_with_known_or_facts_in_environment(&self.runtime_context.builtin_environment, or_fact, verify_state)?;
        if result.is_true() {
            return Ok(result);
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_or_fact_with_known_or_facts_in_environment(
        environment: &Environment,
        given_or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        if let Some(known_or_facts) = environment.known_or_facts.get(&given_or_fact.key()) {
            for known_or_fact in known_or_facts.iter() {
                let or_facts_match = Self::verify_or_fact_matches_known_or_fact_in_environment(
                    environment,
                    given_or_fact,
                    known_or_fact,
                    verify_state,
                )?;
                if or_facts_match {
                    return Ok(NonErrStmtExecResult::FactVerifiedByFact(FactVerifiedByFact::new(
                        given_or_fact.to_string(),
                        known_or_fact.to_string(),
                        InferResult::new(),
                        given_or_fact.line_file_index,
                        known_or_fact.line_file_index,
                    )));
                }
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn verify_or_fact_matches_known_or_fact_in_environment(
        environment: &Environment,
        given_or_fact: &OrFact,
        known_or_fact: &OrFact,
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        if given_or_fact.facts.len() != known_or_fact.facts.len() {
            return Ok(false);
        }

        for (given_branch, known_branch) in given_or_fact.facts.iter().zip(known_or_fact.facts.iter()) {
            let branch_matches = Self::verify_or_branch_matches_known_or_branch_in_environment(
                environment,
                given_branch,
                known_branch,
                verify_state,
            )?;
            if !branch_matches {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn verify_or_branch_matches_known_or_branch_in_environment(
        environment: &Environment,
        given_branch: &AndChainAtomicFact,
        known_branch: &AndChainAtomicFact,
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        match (given_branch, known_branch) {
            (AndChainAtomicFact::AtomicFact(given_atomic_fact), AndChainAtomicFact::AtomicFact(known_atomic_fact)) => {
                Self::verify_atomic_fact_matches_known_atomic_fact_for_or_fact_in_environment(
                    environment,
                    given_atomic_fact,
                    known_atomic_fact,
                    verify_state,
                )
            }
            (AndChainAtomicFact::AndFact(_), AndChainAtomicFact::AndFact(_)) => Ok(true),
            (AndChainAtomicFact::ChainFact(_), AndChainAtomicFact::ChainFact(_)) => Ok(true),
            _ => Ok(false),
        }
    }

    fn verify_atomic_fact_matches_known_atomic_fact_for_or_fact_in_environment(
        environment: &Environment,
        given_atomic_fact: &AtomicFact,
        known_atomic_fact: &AtomicFact,
        _verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        if !given_atomic_fact.is_the_same_fact_type(known_atomic_fact) {
            return Ok(false);
        }
        if given_atomic_fact.args().len() != known_atomic_fact.args().len() {
            return Ok(false);
        }

        for (given_arg, known_arg) in given_atomic_fact.args().iter().zip(known_atomic_fact.args().iter()) {
            if !Self::verify_two_objs_are_equal_in_environment(environment, given_arg, known_arg) {
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn verify_two_objs_are_equal_in_environment(environment: &Environment, left_obj: &crate::obj::Obj, right_obj: &crate::obj::Obj) -> bool {
        let left_string = left_obj.to_string();
        let right_string = right_obj.to_string();
        if left_string == right_string {
            return true;
        }

        let known_left = environment.known_equality.get(&left_string);
        let known_right = environment.known_equality.get(&right_string);
        match (known_left, known_right) {
            (Some(left_equal_class), Some(right_equal_class)) => std::rc::Rc::ptr_eq(left_equal_class, right_equal_class),
            _ => false,
        }
    }
}