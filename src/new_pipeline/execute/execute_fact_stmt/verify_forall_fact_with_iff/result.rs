use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum VerifyForallFactWithIffResult {
    Success(VerifyForallFactWithIffSuccess),
    Failed(VerifyForallFactWithIffFailed),
}

pub struct VerifyForallFactWithIffSuccess {}

pub enum VerifyForallFactWithIffFailed {
    FailToSearchProof,
}

impl VerifyForallFactWithIffResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn forall_fact_with_iff_result_from_search_fail() -> VerifyFactResult {
    VerifyFactResult::ForallFactWithIff(Box::new(VerifyForallFactWithIffResult::Failed(
        VerifyForallFactWithIffFailed::FailToSearchProof,
    )))
}
