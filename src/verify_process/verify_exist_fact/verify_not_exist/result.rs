use crate::prelude::*;

pub struct VerifyNotExistFactResult {
    pub fact: ExistentialSpec,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: NotExistFactSearchedProof,
}

pub enum NotExistFactSearchedProof {
    ByCache(CacheSearchProof),
    ByDemorganForall(VerifyForallFactResult),
}
