//! Atomic-fact verification dispatch.

use crate::error::RuntimeError;
use crate::fact::{AtomicFact, Fact};
use crate::result::{ProveFactResult, VerifyFactResult};
use crate::runtime::Runtime;
use crate::verification::{AlternateFactSearch, VerifyState};

impl Runtime {
    fn verify_atomic_fact_family_after_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => {
                self.verify_atomic_except_equality(fact, verify_state, AlternateFactSearch::Enabled)
            }
        }
    }

    pub(in crate::verification) fn prove_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&fact.clone().into())
        {
            return Ok(cached_result);
        }
        if let Some(cached_result) =
            self.verification_result_from_proof_search_memo(fact, verify_state)
        {
            return Ok(cached_result);
        }

        let state_after_well_definedness = verify_state.clone();

        if let Some((reduced_fact, evidence)) =
            self.transparent_definition_reduction_for_atomic_fact(fact)?
        {
            let reduced_result = self.verify_atomic_fact_family_after_well_definedness(
                &reduced_fact,
                &state_after_well_definedness,
            )?;
            if reduced_result.is_success() {
                let result = self.retarget_transparent_definition_reduction_result(
                    fact,
                    reduced_result,
                    evidence,
                );
                return Ok(self.remember_successful_atomic_fact_for_proof_search(
                    fact,
                    result,
                    verify_state,
                ));
            }
        }

        let result = self.verify_atomic_fact_family_after_well_definedness(
            fact,
            &state_after_well_definedness,
        )?;
        Ok(self.remember_successful_atomic_fact_for_proof_search(fact, result, verify_state))
    }

    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        self.verify_fact_allow_unknown(&Fact::from(fact.clone()), verify_state)
    }
}
