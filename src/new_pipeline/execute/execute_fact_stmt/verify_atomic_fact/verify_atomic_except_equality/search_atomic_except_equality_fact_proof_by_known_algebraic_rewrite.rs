use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::PropAlgebraicPropertyId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

// Known / registered algebraic rewrite for atomic-except-equality facts.
//
// Distinct from opaque resolve_obj: cites a PropAlgebraicPropertyId (or proves
// an alternate fact) instead of silently rewriting objects in Runtime.
//
// Examples (future):
// - Reflexivity: prove `a <= a` from a registered reflexive property.
// - Symmetry: prove `a != b` from alternate `b != a` via registered symmetry.
//
// Search currently always returns None.
pub enum AtomicExceptEqualityFactSearchProofByKnownAlgebraicRewrite {
    Reflexivity(AtomicExceptEqualityFactSearchProofByKnownReflexivity),
    Symmetry(AtomicExceptEqualityFactSearchProofByKnownSymmetry),
}

pub struct AtomicExceptEqualityFactSearchProofByKnownReflexivity {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId,
}

pub struct AtomicExceptEqualityFactSearchProofByKnownSymmetry {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId,
    pub argument_permutation: Vec<usize>,
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}

impl Runtime {
    // Placeholder search for known algebraic rewrite (atomic-except-equality).
    // Gated by VerifyState::can_use_algebraic_rewrite in the parent search.
    pub fn search_atomic_except_equality_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        _fact: &AtomicFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAlgebraicRewrite>> {
        Ok(None)
    }
}
