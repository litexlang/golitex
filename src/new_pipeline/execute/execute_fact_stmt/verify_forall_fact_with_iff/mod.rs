mod result;
mod verify_forall_fact_with_iff;
mod well_defined_result;

pub use result::{
    forall_fact_with_iff_result_from_iff_implies_then_fail,
    forall_fact_with_iff_result_from_success,
    forall_fact_with_iff_result_from_then_implies_iff_fail, VerifyForallFactWithIffFailed,
    VerifyForallFactWithIffResult, VerifyForallFactWithIffSuccess,
};
pub use well_defined_result::FailToVerifyForallFactWithIffWellDefinedResult;
