use crate::ast::fact::ForallFactWithIff;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum VerifyForallFactWithIffResult {
    Success(VerifyForallFactWithIffSuccess),
    Failed(VerifyForallFactWithIffFailed),
}

// Stage order: then⇒iff, then iff⇒then. Each direction is a full forall verify.
pub struct VerifyForallFactWithIffSuccess {
    pub fact: ForallFactWithIff,
    pub then_implies_iff: VerifyFactResult,
    pub iff_implies_then: VerifyFactResult,
}

pub enum VerifyForallFactWithIffFailed {
    FailThenImpliesIff {
        fact: ForallFactWithIff,
        then_implies_iff: VerifyFactResult,
    },
    FailIffImpliesThen {
        fact: ForallFactWithIff,
        then_implies_iff: VerifyFactResult,
        iff_implies_then: VerifyFactResult,
    },
}

impl VerifyForallFactWithIffResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn forall_fact_with_iff_result_from_success(
    fact: &ForallFactWithIff,
    then_implies_iff: VerifyFactResult,
    iff_implies_then: VerifyFactResult,
) -> VerifyFactResult {
    VerifyFactResult::ForallFactWithIff(Box::new(VerifyForallFactWithIffResult::Success(
        VerifyForallFactWithIffSuccess {
            fact: fact.clone(),
            then_implies_iff,
            iff_implies_then,
        },
    )))
}

pub fn forall_fact_with_iff_result_from_then_implies_iff_fail(
    fact: &ForallFactWithIff,
    then_implies_iff: VerifyFactResult,
) -> VerifyFactResult {
    VerifyFactResult::ForallFactWithIff(Box::new(VerifyForallFactWithIffResult::Failed(
        VerifyForallFactWithIffFailed::FailThenImpliesIff {
            fact: fact.clone(),
            then_implies_iff,
        },
    )))
}

pub fn forall_fact_with_iff_result_from_iff_implies_then_fail(
    fact: &ForallFactWithIff,
    then_implies_iff: VerifyFactResult,
    iff_implies_then: VerifyFactResult,
) -> VerifyFactResult {
    VerifyFactResult::ForallFactWithIff(Box::new(VerifyForallFactWithIffResult::Failed(
        VerifyForallFactWithIffFailed::FailIffImpliesThen {
            fact: fact.clone(),
            then_implies_iff,
            iff_implies_then,
        },
    )))
}
