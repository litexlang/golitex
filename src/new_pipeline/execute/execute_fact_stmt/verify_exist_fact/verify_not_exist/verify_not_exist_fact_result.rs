use crate::fact::PlainExistFact;
use crate::prelude::*;

pub struct VerifyNotExistFactResult {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: NotExistFactSearchedProof,
}

pub enum NotExistFactSearchedProof {
    ByCache(CacheSearchProof),
    ByDemorganForall(VerifyForallFactResult),
}
