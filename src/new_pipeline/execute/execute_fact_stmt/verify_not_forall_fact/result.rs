use crate::new_pipeline::ast::fact::{ExistShapedFact, NotForallFact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;

pub enum VerifyNotForallFactResult {
    Success(VerifyNotForallFactSuccess),
    Failed(VerifyNotForallFactFailed),
}

// Prove by De Morgan counterexample exist, then reuse exist verify.
pub struct VerifyNotForallFactSuccess {
    pub fact: NotForallFact,
    pub derived_exist: ExistShapedFact,
    pub prove_derived_exist: VerifyFactResult,
}

pub enum VerifyNotForallFactFailed {
    // Then/dom negation cannot be expressed as QuantifierFreeFact (e.g. FnEqual*).
    UnsupportedNegation {
        fact: NotForallFact,
    },
    FailToProveDerivedExist {
        fact: NotForallFact,
        derived_exist: ExistShapedFact,
        prove_derived_exist: VerifyFactResult,
    },
}

impl VerifyNotForallFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn not_forall_fact_result_from_success(
    fact: &NotForallFact,
    derived_exist: ExistShapedFact,
    prove_derived_exist: VerifyFactResult,
) -> VerifyFactResult {
    VerifyFactResult::NotForall(Box::new(VerifyNotForallFactResult::Success(
        VerifyNotForallFactSuccess {
            fact: fact.clone(),
            derived_exist,
            prove_derived_exist,
        },
    )))
}

pub fn not_forall_fact_result_from_unsupported(fact: &NotForallFact) -> VerifyFactResult {
    VerifyFactResult::NotForall(Box::new(VerifyNotForallFactResult::Failed(
        VerifyNotForallFactFailed::UnsupportedNegation {
            fact: fact.clone(),
        },
    )))
}

pub fn not_forall_fact_result_from_exist_fail(
    fact: &NotForallFact,
    derived_exist: ExistShapedFact,
    prove_derived_exist: VerifyFactResult,
) -> VerifyFactResult {
    VerifyFactResult::NotForall(Box::new(VerifyNotForallFactResult::Failed(
        VerifyNotForallFactFailed::FailToProveDerivedExist {
            fact: fact.clone(),
            derived_exist,
            prove_derived_exist,
        },
    )))
}
