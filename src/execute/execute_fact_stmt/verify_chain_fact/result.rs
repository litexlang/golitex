use crate::ast::fact::ChainFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;

pub enum VerifyChainFactResult {
    Success(VerifyChainFactSuccess),
    Failed(VerifyChainFactFailed),
}

pub struct VerifyChainFactSuccess {
    pub fact: ChainFact,
    pub adjacent: Vec<VerifyFactResult>,
    pub known_forall: Option<SearchProofByKnownForallFact>,
}

// Soft miss keeps the child VerifyFactResult as-is (WD detail stays inside it).
pub enum VerifyChainFactFailed {
    FailToVerifyWellDefined {
        fact: ChainFact,
        failed_index: usize,
        succeeded_adjacent: Vec<VerifyFactResult>,
        failed_adjacent: VerifyFactResult,
    },
    FailToSearchProof {
        fact: ChainFact,
        failed_index: usize,
        succeeded_adjacent: Vec<VerifyFactResult>,
        failed_adjacent: VerifyFactResult,
    },
}

impl VerifyChainFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn chain_fact_result_from_adjacent_fail(
    fact: &ChainFact,
    failed_index: usize,
    succeeded_adjacent: Vec<VerifyFactResult>,
    failed_adjacent: VerifyFactResult,
) -> VerifyFactResult {
    let failed = if failed_adjacent.is_wd_failed() {
        VerifyChainFactFailed::FailToVerifyWellDefined {
            fact: fact.clone(),
            failed_index,
            succeeded_adjacent,
            failed_adjacent,
        }
    } else {
        VerifyChainFactFailed::FailToSearchProof {
            fact: fact.clone(),
            failed_index,
            succeeded_adjacent,
            failed_adjacent,
        }
    };
    VerifyFactResult::ChainFact(Box::new(VerifyChainFactResult::Failed(failed)))
}

pub fn chain_fact_result_from_success(
    fact: &ChainFact,
    adjacent: Vec<VerifyFactResult>,
    known_forall: Option<SearchProofByKnownForallFact>,
) -> VerifyFactResult {
    VerifyFactResult::ChainFact(Box::new(VerifyChainFactResult::Success(
        VerifyChainFactSuccess {
            fact: fact.clone(),
            adjacent,
            known_forall,
        },
    )))
}
