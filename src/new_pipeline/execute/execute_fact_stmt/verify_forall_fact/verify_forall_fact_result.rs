use crate::prelude::*;

pub struct VerifyForallFactResult {
    pub fact: ForallFact,
    pub well_defined_proof: ForallFactWellDefinedProof,

    // Keep the local env so later consumers (including Lean compilation) can
    // resolve FactIds that only exist in this temporary proof scope.
    pub local_env: Environment,

    pub local_proof_results: VerifyForallFactProofLocalResults,
}

// These fields mirror the operations performed inside the temporary proof
// environment and travel together as the local part of the forall result.
pub struct VerifyForallFactProofLocalResults {
    pub local_param_def_results: LocalParamsDefResults,
    pub assumption_results: Vec<AssumptionResult>,
    pub verify_result_of_then_facts: Vec<VerifyFactResult>,
}
