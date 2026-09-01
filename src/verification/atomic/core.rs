//! Atomic-fact verification dispatch.

use crate::error::{RuntimeError, RuntimeErrorStruct, VerifyRuntimeError};
use crate::fact::{AtomicFact, Fact};
use crate::result::StmtResult;
use crate::runtime::Runtime;
use crate::verification::{AlternateFactSearch, VerifyState};

impl Runtime {
    fn verify_atomic_fact_family_after_well_definedness(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_non_equational_atomic_fact(
                fact,
                verify_state,
                AlternateFactSearch::Enabled,
            ),
        }
    }

    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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

        if !verify_state.well_definedness_verified {
            if let Err(error) = self.verify_atomic_fact_well_defined(fact, verify_state) {
                return Err({
                    VerifyRuntimeError(RuntimeErrorStruct::new(
                        Some(Fact::from(fact.clone()).into_stmt()),
                        String::new(),
                        fact.line_file(),
                        Some(error),
                        vec![],
                    ))
                    .into()
                });
            }
        }

        let state_after_well_definedness = verify_state.with_well_definedness_verified();

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
}
