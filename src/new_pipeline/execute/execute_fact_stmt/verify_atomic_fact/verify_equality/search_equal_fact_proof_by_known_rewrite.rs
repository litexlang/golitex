use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::PropRewritePropertyId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Known / registered rewrite for EqualFact.
//
// Distinct from opaque resolve_obj: uses an explicit registered property id
// (or similar cite), not Runtime-side silent folding.
//
// Example (future): a registered congruence/simplification lemma applied to
// an equality goal, with `cite_prop_rewrite_property_id` in the Result.
//
// Search currently always returns None.
pub enum EqualitySearchProofByKnownRewrite {
    RegisteredProperty(RegisteredEqualityRewriteProof),
}

// Placeholder payload for a cited registered equality rewrite property.
pub struct RegisteredEqualityRewriteProof {
    pub cite_prop_rewrite_property_id: PropRewritePropertyId,
}

impl Runtime {
    // Placeholder search for equality known rewrite.
    // See EqualitySearchProofByKnownRewrite.
    pub fn search_equal_fact_proof_by_known_rewrite(
        &mut self,
        _fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByKnownRewrite>> {
        Ok(None)
    }
}
