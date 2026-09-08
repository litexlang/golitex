use crate::prelude::*;

pub struct VerifyNotForallFactResult {
    pub fact: NotForallFact,
    pub well_defined_result: VerifyNotForallFactWellDefinednessResult,
    pub searched_proof: NotForallFactSearchedProof,
}

pub enum NotForallFactSearchedProof {
    ByCache(CacheSearchProof),
}
