use crate::new_pipeline::execution_environment::ExecEnv;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::prelude::*;

use super::super::VerifyState;
use super::verify_equality::verification_and_result::DraftEqualitySearchedProof;
use super::verify_non_equational_atomic_fact::verification_and_result::
    NonEquationalAtomicFactSearchedProof;

pub enum VerifyAtomicFactSearchProof {
    Equality(DraftEqualitySearchedProof),
    NonEquationalAtomicFact(NonEquationalAtomicFactSearchedProof),
}

impl Runtime {
    pub fn current_atomic_fact_search_environments(&self) -> impl Iterator<Item = &ExecEnv> {
        self.execution_environments_stack
            .iter()
            .rev()
            .map(Box::as_ref)
    }

    pub fn current_atomic_fact_search_environment_count(&self) -> usize {
        self.current_atomic_fact_search_environments().count()
    }

    pub fn verify_atomic_fact_search_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactSearchProof> {
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();
        let search_state = verify_state.without_well_defined_storage();

        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactSearchProof::Equality(
                self.search_draft_equal_fact_proof(equal_fact, search_state)?,
            )),
            _ => Ok(
                VerifyAtomicFactSearchProof::NonEquationalAtomicFact(
                    self.search_non_equational_atomic_fact_proof(fact, search_state)?,
                ),
            ),
        }
    }
}
