use crate::prelude::*;

pub struct VerifyNotExistFactResult {
    pub fact: ExistentialSpec,
    pub well_defined_result: VerifyExistFactWellDefinednessResult,
    pub searched_proof: NotExistFactSearchedProof,
}

pub struct NotExistFactSearchedProof {
    pub demorgan_forall: VerifyForallFactResult,
}
