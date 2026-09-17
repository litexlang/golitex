mod result;
mod verify_exist_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    exist_fact_result_from_search_fail, exist_fact_result_from_success,
    exist_fact_result_from_wd_fail, ExistFactSearchProofByBuiltinRule,
    ExistFactSearchProofByKnownExistFact, ExistFactSearchedProof, VerifyExistFactFailed,
    VerifyExistFactResult, VerifyExistUniqueFactResult, VerifyExistUniqueFactSuccess,
    VerifyNotExistFactResult, VerifyNotExistFactSuccess, VerifyPlainExistFactResult,
    VerifyPlainExistFactSuccess,
};
pub use well_defined_result::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
    VerifyExistFactWellDefinedResult,
};
