use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;

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
