use crate::prelude::*;

pub struct VerifyNotForallFactResult {
    pub fact: NotForallFact,
    pub well_defined_proof: NotForallFactWellDefinedProof,
    pub searched_proof: NotForallFactSearchedProof,
}

pub enum NotForallFactSearchedProof {
    ByCache(CacheSearchProof),
}
