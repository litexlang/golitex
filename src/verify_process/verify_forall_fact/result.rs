use crate::prelude::*;

pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub well_defined_result: VerifyForallFactWellDefinednessResult,
    pub searched_proof: ForallFactSearchedProof,
}

pub struct ForallFactSearchedProof {
    pub proof_of_each_then_fact: Vec<VerifyFactResult>,
}
