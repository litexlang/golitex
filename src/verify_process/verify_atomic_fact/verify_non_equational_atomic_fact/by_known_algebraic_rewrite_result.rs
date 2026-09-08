use crate::prelude::*;

pub enum NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite {
    Reflexivity(NonEquationalAtomicFactSearchProofByKnownReflexivity),
    Symmetry(NonEquationalAtomicFactSearchProofByKnownSymmetry),
}

pub struct NonEquationalAtomicFactSearchProofByKnownReflexivity {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId,
}

pub struct NonEquationalAtomicFactSearchProofByKnownSymmetry {
    pub cite_prop_algebraic_property_id: PropAlgebraicPropertyId,
    pub argument_permutation: Vec<usize>,
    pub alternate_fact: FactStmt,
    pub proof_of_alternate_fact: VerifyFactResult,
}
