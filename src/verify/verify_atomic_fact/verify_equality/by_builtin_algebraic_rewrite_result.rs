use crate::prelude::*;
use crate::verify_rewrite::VerifyState2;

pub enum EqualitySearchProofByBuiltinAlgebraicRewrite2 {
    ZeroEqualsDifferenceImpliesEqual(EqualitySearchProofByBuiltinZeroEqualsDifference2),
    EqualitySymmetry(EqualitySearchProofByBuiltinEqualitySymmetry2),
}

pub struct EqualitySearchProofByBuiltinZeroEqualsDifference2 {
    pub cite_or_subproof: VerifyFactResult2,
}

pub struct EqualitySearchProofByBuiltinEqualitySymmetry2 {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult2,
}
