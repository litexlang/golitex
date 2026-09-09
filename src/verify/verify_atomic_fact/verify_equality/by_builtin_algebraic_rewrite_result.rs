use crate::prelude::*;
use crate::verify_rewrite::VerifyState;
use crate::verify_rewrite::FactStmt;

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
