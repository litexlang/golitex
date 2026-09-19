//! Requirement-fact verification for object WD (new_pipeline AST).
//!
//! Mirrors old target_requirements: after child WD, prove domain facts true.
//! Search miss returns Ok(branch Failed), same as fact proof search — not Err.

use crate::new_pipeline::ast::fact::{AtomicFact, InFact, QuantifierFreeFact};
use crate::new_pipeline::ast::obj::{Obj, StandardSet};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    atomic_except_equality_fact_result_from_search_fail,
    atomic_except_equality_fact_result_from_success,
    atomic_except_equality_fact_result_from_wd_fail,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyAtomicFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::instantiate::quantifier_free_fact_to_fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Prove one atomic requirement. Ok(Failed) if WD or truth search fails.
    pub(super) fn verify_required_atomic_fact(
        &mut self,
        fact: AtomicFact,
        verify_state: VerifyState,
        _failure_message: String,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof = match self
            .verify_atomic_fact_well_definedness(&fact, verify_state.clone())?
        {
            VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
            VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                return Ok(atomic_except_equality_fact_result_from_wd_fail(reason));
            }
        };
        match self.search_atomic_except_equality_fact_proof(&fact, verify_state)? {
            Some(searched_proof) => Ok(atomic_except_equality_fact_result_from_success(
                &fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(atomic_except_equality_fact_result_from_search_fail(
                &fact,
                well_defined_proof,
            )),
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

    // Prove a FnSet domain fact (already instantiated at the call site).
    pub(super) fn verify_required_quantifier_free_fact(
        &mut self,
        fact: QuantifierFreeFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        self.verify_fact(&quantifier_free_fact_to_fact(fact), verify_state)
    }
}
