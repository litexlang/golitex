use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::runtime::PropAlgebraicPropertyId;
use crate::prelude::*;

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
    pub fn search_atomic_except_equality_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByKnownAlgebraicRewrite>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
