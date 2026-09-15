//! Requirement-fact verification for object WD (new_pipeline AST).
//!
//! Mirrors old target_requirements: after child WD, prove domain facts true.
//! Search miss returns Ok(FailTo*), same as fact proof search — not Err.

use crate::new_pipeline::ast::fact::{AtomicFact, InFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::VerifyAtomicExceptEqualityFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::{
    VerifyFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove one atomic requirement. Ok(FailTo*) if WD or truth search fails.
    pub(super) fn verify_required_atomic_fact(
        &mut self,
        fact: AtomicFact,
        verify_state: VerifyState,
        _failure_message: String,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness(&fact, verify_state.clone())?;
        if well_defined_proof.is_failed() {
            return Ok(VerifyFactResult::FailToVerifyWellDefined);
        }
        match self.search_atomic_except_equality_fact_proof(&fact, verify_state)? {
            Some(searched_proof) => Ok(VerifyFactResult::AtomicExceptEquality(Box::new(
                VerifyAtomicExceptEqualityFactResult {
                    fact,
                    well_defined_proof,
                    searched_proof,
                },
            ))),
            None => Ok(VerifyFactResult::FailToSearchProof),
        }
    }

    pub(super) fn require_obj_in_standard_set(
        &mut self,
        obj: &Obj,
        set: StandardSet,
        verify_state: VerifyState,
        failure_message: String,
    ) -> RuntimeResult<VerifyFactResult> {
        let fact = AtomicFact::InFact(InFact {
            fact_id: self.ids.allocate_fact_id(),
            element: obj.clone(),
            set: Obj::StandardSet(set),
            line_file: None,
        });
        self.verify_required_atomic_fact(fact, verify_state, failure_message)
    }

    pub(super) fn require_obj_in_c(
        &mut self,
        obj: &Obj,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        self.require_obj_in_standard_set(
            obj,
            StandardSet::C,
            verify_state,
            "obj is not in C".to_string(),
        )
    }
}
