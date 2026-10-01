use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{AtomicFact, NotSupersetFact};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not A $superset B`.
pub enum NotSupersetFactSearchProofByBuiltinRule {
    // Duality: known `not B $subset A` proves `not A $superset B`.
    // Example: trust `not {1} $subset {2}`; prove `not {2} $superset {1}`.
    FromKnownNotSubset(FromKnownNotSubsetBuiltinRuleProof),
}

pub struct FromKnownNotSubsetBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    pub fn search_not_superset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSupersetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSupersetFactSearchProofByBuiltinRule>> {
        if let Some(premise_proof) = self.known_not_subset_proof(&fact.right, &fact.left) {
            return Ok(Some(
                NotSupersetFactSearchProofByBuiltinRule::FromKnownNotSubset(
                    FromKnownNotSubsetBuiltinRuleProof { premise_proof },
                ),
            ));
        }
        Ok(None)
    }


}
