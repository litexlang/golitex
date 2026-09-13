use crate::prelude::*;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;

pub struct VerifyForallFactWithIffResult {
    pub fact: ForallFactWithIff,
    pub well_defined_proof: ForallFactWithIffWellDefinedProof,

    // Both directions are ordinary forall proofs. Keep them on the outer
    // result so a consumer can follow the complete iff proof without a
    // nested search enum.
    pub then_implies_iff: VerifyForallFactResult,
    pub iff_implies_then: VerifyForallFactResult,
}
