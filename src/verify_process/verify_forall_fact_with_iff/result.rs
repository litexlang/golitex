use crate::prelude::*;

pub struct VerifyForallFactWithIffResult {
    pub fact: ForallFactWithIff,
    pub well_defined_result: VerifyForallFactWithIffWellDefinednessResult,
    pub searched_proof: ForallFactWithIffSearchedProof,
}

pub struct ForallFactWithIffSearchedProof {
    pub then_implies_iff: VerifyForallFactResult,
    pub iff_implies_then: VerifyForallFactResult,
}
