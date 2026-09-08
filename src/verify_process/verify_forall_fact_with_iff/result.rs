use crate::prelude::*;

pub struct VerifyForallFactWithIffResult {
    pub fact: ForallFactWithIff,
    pub well_defined_proof: ForallFactWithIffWellDefinedProof,
    pub searched_proof: ForallFactWithIffSearchedProof,
}

pub struct ForallFactWithIffSearchedProof {
    pub then_implies_iff: VerifyForallFactResult,
    pub iff_implies_then: VerifyForallFactResult,
}
