use crate::prelude::*;

pub struct VerifyOrFactResult {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof,
    pub searched_proof: OrFactSearchedProof,
}

pub struct OrFactSearchedProof {
    pub chosen_branch_index: usize,
    pub proof_of_chosen_branch: VerifyFactResult,
}
