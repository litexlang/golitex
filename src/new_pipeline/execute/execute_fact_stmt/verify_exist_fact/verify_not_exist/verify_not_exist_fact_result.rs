use crate::fact::PlainExistFact;
use crate::prelude::*;

pub struct VerifyNotExistFactResult {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: NotExistFactSearchedProof,
}

// Exact FactIR ByCache is handled at verify_fact; not-exist uses other search routes.
pub enum NotExistFactSearchedProof {
    ByDemorganForall(VerifyForallFactResult),
}
