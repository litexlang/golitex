use crate::prelude::*;

pub struct VerifyExistUniqueFactResult {
    pub fact: ExistUniqueFact,
    pub well_defined_proof: ExistUniqueFactWellDefinedProof,
    pub searched_proof: ExistUniqueFactSearchedProof,
}

pub struct ExistUniqueFactSearchedProof {
    pub proof_of_exist_fact: VerifyPlainExistFactResult,
    pub proof_of_uniqueness: VerifyForallFactResult,
}
