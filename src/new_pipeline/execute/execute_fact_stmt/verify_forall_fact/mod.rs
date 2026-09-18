mod result;
mod verify_forall_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    forall_fact_result_from_success, forall_fact_result_from_then_fail,
    forall_fact_result_from_wd_fail, AssumeDomFactResult, ProveAndStoreThenFactResult,
    VerifyForallFactFailed, VerifyForallFactResult, VerifyForallFactSuccess,
};
pub use well_defined_result::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
    VerifyForallFactWellDefinedResult,
};
