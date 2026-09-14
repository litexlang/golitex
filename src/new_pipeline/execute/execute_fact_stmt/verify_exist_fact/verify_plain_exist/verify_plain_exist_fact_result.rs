use crate::fact::PlainExistFact;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::prelude::*;

pub struct VerifyPlainExistFactResult {
    pub fact: PlainExistFact,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: PlainExistFactSearchedProof,
}

// Exact FactIR ByCache is handled at verify_fact; plain exist uses other search routes.
pub enum PlainExistFactSearchedProof {
    ByBuiltinRule(PlainExistFactSearchedProofByBuiltinRule),
    ByKnownExistFact(PlainExistFactSearchedProofByKnownExistFact),
    ByKnownForallFact(PlainExistFactSearchedProofByKnownForallFact),
}

pub struct PlainExistFactSearchedProofByKnownExistFact {
    pub cite_fact_id: FactId,
    // If known-exist matching requires alpha-normalized string equality of the
    // full body, cite_fact_id alone is enough.
}

pub struct PlainExistFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}
