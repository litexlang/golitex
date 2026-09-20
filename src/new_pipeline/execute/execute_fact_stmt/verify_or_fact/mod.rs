mod helper;
mod result;
mod search_or_fact_proof_by_builtin_rule;
mod verify_or_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    AssumeNegatedOrBranchResult, OrBuiltinRealLineTrichotomyEqLessGreater,
    OrBuiltinRealLineTrichotomyGreaterEqLess, OrBuiltinRealLineTrichotomyLessEqGreater,
    OrFactSearchProofByBuiltinRule, OrFactSearchProofByKnownOrFact,
    OrFactSearchProofBySelectedBranch, OrFactSearchedProof, VerifyOrFactFailed, VerifyOrFactResult,
    VerifyOrFactSuccess,
};
pub use well_defined_result::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof, VerifyOrFactWellDefinedResult,
};
