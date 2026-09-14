use crate::prelude::*;

pub struct VerifyOrFactResult {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof,
    pub searched_proof: OrFactSearchedProof,
}

// Exact FactIR ByCache is AtomicFact-only; or-facts use branch search.
pub enum OrFactSearchedProof {
    ByChosenBranch {
        chosen_branch_index: usize,
        proof_of_chosen_branch: VerifyFactResult,
    },
}
