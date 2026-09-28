use crate::ast::fact::AndFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;

pub enum VerifyAndFactResult {
    Success(VerifyAndFactSuccess),
    Failed(VerifyAndFactFailed),
}

pub struct VerifyAndFactSuccess {
    pub fact: AndFact,
    pub components: Vec<VerifyFactResult>,
    pub known_forall: Option<SearchProofByKnownForallFact>,
}

// And has no separate top-level WD stage: each conjunct runs WD+search.
// Soft miss keeps the child VerifyFactResult as-is (WD detail stays inside it).
pub enum VerifyAndFactFailed {
    FailToVerifyWellDefined {
        fact: AndFact,
        failed_index: usize,
        succeeded_components: Vec<VerifyFactResult>,
        failed_component: VerifyFactResult,
    },
    FailToSearchProof {
        fact: AndFact,
        failed_index: usize,
        succeeded_components: Vec<VerifyFactResult>,
        failed_component: VerifyFactResult,
    },
}

impl VerifyAndFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn and_fact_result_from_component_fail(
    fact: &AndFact,
    failed_index: usize,
    succeeded_components: Vec<VerifyFactResult>,
    failed_component: VerifyFactResult,
) -> VerifyFactResult {
    let failed = if failed_component.is_wd_failed() {
        VerifyAndFactFailed::FailToVerifyWellDefined {
            fact: fact.clone(),
            failed_index,
            succeeded_components,
            failed_component,
        }
    } else {
        VerifyAndFactFailed::FailToSearchProof {
            fact: fact.clone(),
            failed_index,
            succeeded_components,
            failed_component,
        }
    };
    VerifyFactResult::AndFact(Box::new(VerifyAndFactResult::Failed(failed)))
}

pub fn and_fact_result_from_success(
    fact: &AndFact,
    components: Vec<VerifyFactResult>,
    known_forall: Option<SearchProofByKnownForallFact>,
) -> VerifyFactResult {
    VerifyFactResult::AndFact(Box::new(VerifyAndFactResult::Success(
        VerifyAndFactSuccess {
            fact: fact.clone(),
            components,
            known_forall,
        },
    )))
}
