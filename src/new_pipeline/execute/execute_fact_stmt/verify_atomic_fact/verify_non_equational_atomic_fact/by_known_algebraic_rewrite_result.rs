use crate::prelude::*;
use crate::new_pipeline::execute_fact_stmt::VerifyState2;

pub enum NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2 {
    Reflexivity(NonEquationalAtomicFactSearchProofByKnownReflexivity2),
    Symmetry(NonEquationalAtomicFactSearchProofByKnownSymmetry2),
}

pub struct NonEquationalAtomicFactSearchProofByKnownReflexivity2 {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId2,
}

pub struct NonEquationalAtomicFactSearchProofByKnownSymmetry2 {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId2,
    pub argument_permutation: Vec<usize>,
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult2,
}
