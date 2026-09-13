use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub enum EqualitySearchProofByKnownAlgebraicRewrite {
    Transitivity(EqualitySearchProofByKnownTransitivity),
}

pub struct EqualitySearchProofByKnownTransitivity {
    pub middle: Obj,
    pub left_to_middle: VerifyFactResult,
    pub middle_to_right: VerifyFactResult,
}
