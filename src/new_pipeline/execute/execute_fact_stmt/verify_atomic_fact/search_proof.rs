//! Atomic-fact truth-proof search stage.
//!
//! This module is the boundary between atomic-fact well-definedness and
//! truth-proof search.  It deliberately has a narrower view of runtime state
//! than module resolution:
//!
//! * ordinary fact search may inspect only
//!   [`Runtime::execution_environments_stack`];
//! * [`Runtime::module_manager`] is not an input to this stage and must not be
//!   consulted by any of its search slots;
//! * an explicit `by def` / `by thm` directive is a separate operation and is
//!   the only route for resolving a definition or theorem from a loaded
//!   module.
//!
//! The individual slots are intentionally implemented in the equality and
//! non-equational modules.  Keeping the dispatcher here makes the phase
//! boundary explicit without coupling ordinary fact lookup to module lookup.

use crate::prelude::*;
use crate::new_pipeline::execute_fact_stmt::VerifyState2;

use super::verify_equality::verification_and_result::EqualitySearchedProof2;
use super::verify_non_equational_atomic_fact::verification_and_result::
    NonEquationalAtomicFactSearchedProof2;

/// Proof returned by the atomic-fact search phase.
pub enum VerifyAtomicFactSearchProof2 {
    Equality(EqualitySearchedProof2),
    NonEquationalAtomicFact(NonEquationalAtomicFactSearchedProof2),
}

impl Runtime {
    /// Iterate over environments visible to ordinary atomic-fact search.
    ///
    /// The newest execution scope is visited first, followed by its parents.
    /// Keeping this iterator on `Runtime` gives every search slot one explicit
    /// source of truth and makes it impossible to accidentally broaden the
    /// implicit search to the module registry.
    pub fn current_atomic_fact_search_environments(&self) -> impl Iterator<Item = &ExecEnv> {
        self.execution_environments_stack
            .iter()
            .rev()
            .map(Box::as_ref)
    }

    /// Number of execution environments visible to ordinary fact search.
    ///
    /// This small accessor is the intended boundary for the search slots.  It
    /// intentionally exposes no module-manager state: loaded module main
    /// environments are not implicit proof premises.
    pub fn current_atomic_fact_search_environment_count(&self) -> usize {
        self.current_atomic_fact_search_environments().count()
    }

    /// Run the truth-proof phase for one atomic fact.
    ///
    /// Well-definedness is performed by the caller before this method.  The
    /// dispatcher only chooses the equality or non-equational pipeline.  Both
    /// pipelines must search the current execution-environment stack (and its
    /// visible parent scopes) only; they must never fall back to
    /// `module_manager`.
    pub fn verify_atomic_fact_search_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> Result<VerifyAtomicFactSearchProof2, RuntimeError> {
        // Keep the search boundary observable at the phase entry.  The value
        // is intentionally not used to select a different source: an empty
        // stack simply means that no ordinary environment facts are visible.
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();
        let search_state = verify_state.without_well_defined_storage();

        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(
                VerifyAtomicFactSearchProof2::Equality(
                    self.search_equal_fact_proof2(equal_fact, search_state)?,
                ),
            ),
            _ => Ok(
                VerifyAtomicFactSearchProof2::NonEquationalAtomicFact(
                    self.search_non_equational_atomic_fact_proof2(fact, search_state)?,
                ),
            ),
        }
    }
}
