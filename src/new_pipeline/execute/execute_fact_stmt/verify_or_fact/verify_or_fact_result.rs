use crate::prelude::*;

pub struct VerifyOrFactResult {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof,
    pub searched_proof: OrFactSearchedProof,
}

pub enum OrFactSearchedProof {
    ByCache(CacheSearchProof),
    ByChosenBranch {
        chosen_branch_index: usize,
        proof_of_chosen_branch: VerifyFactResult,
    },
}
