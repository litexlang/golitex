use crate::prelude::*;

pub struct VerifyAndFactResult {
    pub fact: AndFact,
    pub well_defined_proof: AndFactWellDefinedProof,

    // Prove every conjunct in source order. Keep the child proofs on the outer
    // result so a consumer can follow the complete and-proof without a nested
    // search struct.
    pub proof_of_each_conjunct: Vec<VerifyFactResult>,
}
