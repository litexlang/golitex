use crate::prelude::*;
use crate::verify_rewrite::VerifyState;

pub enum EqualitySearchProofByKnownAlgebraicRewrite {
    Transitivity(EqualitySearchProofByKnownTransitivity),
}

pub struct EqualitySearchProofByKnownTransitivity {
    pub middle: Obj,
    pub left_to_middle: VerifyFactResult,
    pub middle_to_right: VerifyFactResult,
}
