use crate::prelude::*;

pub struct VerifyChainFactResult {
    pub fact: ChainFact,
    pub well_defined_proof: ChainFactWellDefinedProof,

    // Prove every adjacent comparison in source order. Keep the child proofs on
    // the outer result so a consumer can follow the complete chain proof.
    pub proof_of_each_edge: Vec<VerifyFactResult>,
}
