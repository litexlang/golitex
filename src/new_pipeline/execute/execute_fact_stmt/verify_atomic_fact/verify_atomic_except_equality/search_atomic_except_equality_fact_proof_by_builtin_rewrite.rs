use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Builtin rewrite for atomic-except-equality facts.
//
// Part of replacing legacy opaque resolve_obj: order duals and similar
// rewrites must appear as explicit Result certificates, not silent
// pre-normalization of objects.
//
// Example (OrderDual, future): prove `a > b` by proving alternate `b < a`.
// Search currently always returns None.
pub enum AtomicExceptEqualityFactSearchProofByBuiltinRewrite {
    // Rewrite a goal to an order-dual alternate fact, then prove the alternate.
    // Example: goal `2 > 1` via alternate `1 < 2`.
    OrderDual(AtomicExceptEqualityFactSearchProofByBuiltinOrderDual),
}

pub struct AtomicExceptEqualityFactSearchProofByBuiltinOrderDual {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Placeholder search for builtin rewrite (atomic-except-equality).
    // Gated by VerifyState::can_use_rewrite in the parent search.
    pub fn search_atomic_except_equality_fact_proof_by_builtin_rewrite(
        &mut self,
        _fact: &AtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinRewrite>> {
        Ok(None)
    }
}
