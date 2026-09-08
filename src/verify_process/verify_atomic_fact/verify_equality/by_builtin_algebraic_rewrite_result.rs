use crate::prelude::*;

pub enum EqualitySearchProofByBuiltinAlgebraicRewrite {
    ZeroEqualsDifferenceImpliesEqual(EqualitySearchProofByBuiltinZeroEqualsDifference),
    EqualitySymmetry(EqualitySearchProofByBuiltinEqualitySymmetry),
}

pub struct EqualitySearchProofByBuiltinZeroEqualsDifference {
    pub cite_or_subproof: VerifyFactResult,
}

pub struct EqualitySearchProofByBuiltinEqualitySymmetry {
    pub alternate_fact: FactStmt,
    pub proof_of_alternate_fact: VerifyFactResult,
}
