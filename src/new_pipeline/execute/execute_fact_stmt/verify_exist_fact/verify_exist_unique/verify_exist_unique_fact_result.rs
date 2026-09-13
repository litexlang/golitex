use crate::fact::PlainExistFact;
use crate::prelude::*;

pub struct VerifyExistUniqueFactResult {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: ExistUniqueFactSearchedProof,
}

pub enum ExistUniqueFactSearchedProof {
    ByCache(CacheSearchProof),
    ProveAsExistFactWithUniqueness(ExistUniqueFactSearchedProofByExistAndUniqueness),
}

pub struct ExistUniqueFactSearchedProofByExistAndUniqueness {
    pub proof_of_exist_fact: VerifyPlainExistFactResult,
    pub proof_of_uniqueness: VerifyForallFactResult,
}
