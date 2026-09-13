use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub enum EqualitySearchProofByBuiltinAlgebraicRewrite {
    ZeroEqualsDifferenceImpliesEqual(EqualitySearchProofByBuiltinZeroEqualsDifference),
    EqualitySymmetry(EqualitySearchProofByBuiltinEqualitySymmetry),
}

pub struct EqualitySearchProofByBuiltinZeroEqualsDifference {
    pub cite_or_subproof: VerifyFactResult,
}

pub struct EqualitySearchProofByBuiltinEqualitySymmetry {
    pub alternate_fact: Fact,
    pub proof_of_alternate_fact: VerifyFactResult,
}
