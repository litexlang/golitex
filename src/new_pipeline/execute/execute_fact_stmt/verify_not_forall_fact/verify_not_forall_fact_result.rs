use crate::prelude::*;

pub struct VerifyNotForallFactResult {
    pub fact: NotForallFact,
    pub well_defined_proof: NotForallFactWellDefinedProof,
    pub searched_proof: NotForallFactSearchedProof,
}

// Exact FactIR ByCache is handled at verify_fact; not-forall search routes TBD.
pub enum NotForallFactSearchedProof {}
