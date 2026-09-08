use crate::prelude::*;

pub struct VerifyAndFactResult {
    pub fact: AndFact,
    pub well_defined_result: VerifyAndFactWellDefinednessResult,
    pub searched_proof: AndFactSearchedProof,
}

pub struct AndFactSearchedProof {
    pub proof_of_each_conjunct: Vec<VerifyFactResult>,
}
