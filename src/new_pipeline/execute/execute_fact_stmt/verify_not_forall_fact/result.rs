use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum VerifyNotForallFactResult {
    Success(VerifyNotForallFactSuccess),
    Failed(VerifyNotForallFactFailed),
}

pub struct VerifyNotForallFactSuccess {}

pub enum VerifyNotForallFactFailed {
    FailToSearchProof,
}

impl VerifyNotForallFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn not_forall_fact_result_from_search_fail() -> VerifyFactResult {
    VerifyFactResult::NotForall(Box::new(VerifyNotForallFactResult::Failed(
        VerifyNotForallFactFailed::FailToSearchProof,
    )))
}
