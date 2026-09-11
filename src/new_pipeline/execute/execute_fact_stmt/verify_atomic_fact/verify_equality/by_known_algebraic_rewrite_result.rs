use crate::prelude::*;
use crate::new_pipeline::execute_fact_stmt::VerifyState2;

pub enum EqualitySearchProofByKnownAlgebraicRewrite2 {
    Transitivity(EqualitySearchProofByKnownTransitivity2),
}

pub struct EqualitySearchProofByKnownTransitivity2 {
    pub middle: Obj,
    pub left_to_middle: VerifyFactResult2,
    pub middle_to_right: VerifyFactResult2,
}
