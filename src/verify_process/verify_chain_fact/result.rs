use crate::prelude::*;

pub struct VerifyChainFactResult {
    pub fact: ChainFact,
    pub well_defined_proof: ChainFactWellDefinedProof,
    pub searched_proof: ChainFactSearchedProof,
}

pub struct ChainFactSearchedProof {
    pub proof_of_each_edge: Vec<VerifyFactResult>,
}
