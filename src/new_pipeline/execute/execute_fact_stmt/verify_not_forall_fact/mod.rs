mod derive_exist;
mod result;
mod verify_not_forall_fact;
mod verify_well_defined;
mod well_defined_result;

pub use result::{
    not_forall_fact_result_from_exist_fail, not_forall_fact_result_from_success,
    not_forall_fact_result_from_unsupported, VerifyNotForallFactFailed,
    VerifyNotForallFactResult, VerifyNotForallFactSuccess,
};
pub use well_defined_result::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
    VerifyNotForallFactWellDefinedResult,
};
