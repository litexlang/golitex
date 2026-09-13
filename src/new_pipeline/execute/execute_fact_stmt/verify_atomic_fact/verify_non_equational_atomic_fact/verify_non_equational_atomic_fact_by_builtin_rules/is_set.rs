use crate::new_pipeline::ast::fact::IsSetFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Every well-defined object is a set.
// Example: prove `is_set(1)`, `is_set(R)`, `is_set({x N: x > 0})`.
pub enum IsSetFactSearchProofByBuiltinRule {
    AlwaysTrue(IsSetAlwaysTrueBuiltinRuleProof),
}

pub struct IsSetAlwaysTrueBuiltinRuleProof {}

impl Runtime {
    // Builtin: every well-defined object is a set, so `is_set(t)` always holds.
    // Example: prove `is_set(1)`, `is_set(R)`.
    pub fn search_is_set_fact_proof_by_builtin_rule(
        &mut self,
        fact: &IsSetFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsSetFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(Some(IsSetFactSearchProofByBuiltinRule::AlwaysTrue(
            IsSetAlwaysTrueBuiltinRuleProof {},
        )))
    }
}
