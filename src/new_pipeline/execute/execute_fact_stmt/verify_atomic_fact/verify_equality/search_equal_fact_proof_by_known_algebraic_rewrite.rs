use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::PropAlgebraicPropertyId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Known / registered algebraic rewrite for EqualFact.
//
// Distinct from opaque resolve_obj: uses an explicit registered property id
// (or similar cite), not Runtime-side silent folding.
//
// Example (future): a registered congruence/simplification lemma applied to
// an equality goal, with `cite_prop_algebraic_property_id` in the Result.
//
// Search currently always returns None.
pub enum EqualitySearchProofByKnownAlgebraicRewrite {
    RegisteredProperty(RegisteredEqualityAlgebraicRewriteProof),
}

// Placeholder payload for a cited registered equality rewrite property.
pub struct RegisteredEqualityAlgebraicRewriteProof {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId,
}

impl Runtime {
    // Placeholder search for equality known algebraic rewrite.
    // See EqualitySearchProofByKnownAlgebraicRewrite.
    pub fn search_equal_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        _fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByKnownAlgebraicRewrite>> {
        Ok(None)
    }
}
