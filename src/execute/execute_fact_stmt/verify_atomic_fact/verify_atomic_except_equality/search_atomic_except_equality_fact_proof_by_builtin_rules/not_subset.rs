use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::ast::fact::{AtomicFact, NotSubsetFact};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

// Builtin rules for `not A $subset B`.
pub enum NotSubsetFactSearchProofByBuiltinRule {
    // Duality: known `not B $superset A` proves `not A $subset B`.
    // Example: trust `not {2} $superset {1}`; prove `not {1} $subset {2}`.
    FromKnownNotSuperset(FromKnownNotSupersetBuiltinRuleProof),
}

pub struct FromKnownNotSupersetBuiltinRuleProof {
    pub premise_proof: AtomicExceptEqualityFactKnownProof,
}

impl Runtime {
    pub fn search_not_subset_fact_proof_by_builtin_rule(
        &mut self,
        fact: &NotSubsetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSubsetFactSearchProofByBuiltinRule>> {
        if let Some(premise_proof) = self.known_not_superset_proof(&fact.right, &fact.left) {
            return Ok(Some(
                NotSubsetFactSearchProofByBuiltinRule::FromKnownNotSuperset(
                    FromKnownNotSupersetBuiltinRuleProof { premise_proof },
                ),
            ));
        }
        Ok(None)
    }


}
