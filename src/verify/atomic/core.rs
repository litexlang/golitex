//! Atomic-fact verification dispatch.

use crate::error::{RuntimeError, RuntimeErrorStruct, VerifyRuntimeError};
use crate::fact::{AtomicFact, Fact};
use crate::pipeline::record_pipeline_step;
use crate::result::StmtResult;
use crate::runtime::Runtime;
use crate::verify::{AlternateFactSearch, ProofSearchState};

impl Runtime {
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: &ProofSearchState,
    ) -> Result<StmtResult, RuntimeError> {
        record_pipeline_step(
            "verify",
            "Runtime::verify_atomic_fact",
            "src/verify/atomic/core.rs",
        );
        if let Some(cached_result) =
            self.verification_result_from_known_fact_cache(&fact.clone().into())
        {
            return Ok(cached_result);
        }

        if !verify_state.well_definedness_verified {
            let well_defined_state = verify_state.without_known_forall_for_equality();
            if let Err(error) = self.verify_atomic_fact_well_defined(fact, &well_defined_state) {
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

        let result = match fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact(equal_fact, &state_after_well_definedness)
            }
            _ => self.verify_non_equational_atomic_fact(
                fact,
                &state_after_well_definedness,
                AlternateFactSearch::Enabled,
            ),
        }?;
        Ok(self.cache_successful_atomic_fact_for_statement(fact, result))
    }
}
