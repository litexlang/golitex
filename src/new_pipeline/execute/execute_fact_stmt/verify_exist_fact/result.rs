use crate::new_pipeline::ast::fact::{ExistFactFamily, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::well_defined_result::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::FactId;

// Mirrors ExistFactFamily: plain exist / exist! / not exist are separate owners.
pub enum VerifyExistFactResult {
    PlainExistFact(VerifyPlainExistFactResult),
    ExistUniqueFact(VerifyExistUniqueFactResult),
    NotExistFact(VerifyNotExistFactResult),
}

impl VerifyExistFactResult {
    pub fn is_failed(&self) -> bool {
        match self {
            Self::PlainExistFact(r) => r.is_failed(),
            Self::ExistUniqueFact(r) => r.is_failed(),
            Self::NotExistFact(r) => r.is_failed(),
        }
    }
}

pub enum VerifyPlainExistFactResult {
    Success(VerifyPlainExistFactSuccess),
    Failed(VerifyExistFactFailed),
}

pub enum VerifyExistUniqueFactResult {
    Success(VerifyExistUniqueFactSuccess),
    Failed(VerifyExistFactFailed),
}

pub enum VerifyNotExistFactResult {
    Success(VerifyNotExistFactSuccess),
    Failed(VerifyExistFactFailed),
}

pub struct VerifyPlainExistFactSuccess {
    pub fact: ExistFactFamily,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: ExistFactSearchedProof,
}

pub struct VerifyExistUniqueFactSuccess {
    pub fact: ExistFactFamily,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: ExistFactSearchedProof,
}

pub struct VerifyNotExistFactSuccess {
    pub fact: ExistFactFamily,
    pub well_defined_proof: ExistFactWellDefinedProof,
    pub searched_proof: ExistFactSearchedProof,
}

// Shared fail payload for plain / unique / not-exist (same WD + search stages).
pub enum VerifyExistFactFailed {
    FailToVerifyWellDefined(FailToVerifyExistFactWellDefinedResult),
    FailToSearchProof {
        fact: ExistFactFamily,
        well_defined_proof: ExistFactWellDefinedProof,
    },
}

impl VerifyPlainExistFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl VerifyExistUniqueFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl VerifyNotExistFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// Search order: builtin → known_exist → known_forall.
pub enum ExistFactSearchedProof {
    ByBuiltinRule(ExistFactSearchProofByBuiltinRule),
    ByKnownExistFact(ExistFactSearchProofByKnownExistFact),
    ByKnownForallFact(SearchProofByKnownForallFact),
}

// One exist-builtin rule ↔ one dedicated evidence struct.
pub enum ExistFactSearchProofByBuiltinRule {
    RealLineComparisonWitness(ExistBuiltinRealLineComparisonWitness),
}

// Existential witness on the real line for a comparison atom.
// Mathematical property: for any known real `c`, there exist reals above,
// below, equal to, and distinct from `c`; also there exist pairs `a, b R`
// satisfying any of the six order/equality comparisons.
//
// Examples:
// - `exist x R st {x > 100}` after proving `100 $in R`
// - `exist a, b R st {a > b}` (no free operands)
pub struct ExistBuiltinRealLineComparisonWitness {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct ExistFactSearchProofByKnownExistFact {
    pub cite_fact_id: FactId,
}

// Wrap plain / unique / not-exist into VerifyFactResult::ExistFact(...).

pub fn exist_fact_result_from_wd_fail(
    fact: &ExistFactFamily,
    reason: FailToVerifyExistFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::ExistFact(Box::new(exist_fact_result_failed(
        fact,
        VerifyExistFactFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn exist_fact_result_from_search_fail(
    fact: &ExistFactFamily,
    well_defined_proof: ExistFactWellDefinedProof,
) -> VerifyFactResult {
    VerifyFactResult::ExistFact(Box::new(exist_fact_result_failed(
        fact,
        VerifyExistFactFailed::FailToSearchProof {
            fact: fact.clone(),
            well_defined_proof,
        },
    )))
}

pub fn exist_fact_result_from_success(
    fact: &ExistFactFamily,
    well_defined_proof: ExistFactWellDefinedProof,
    searched_proof: ExistFactSearchedProof,
) -> VerifyFactResult {
    VerifyFactResult::ExistFact(Box::new(match fact {
        ExistFactFamily::Exist(_) => {
            VerifyExistFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(
                VerifyPlainExistFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
        ExistFactFamily::ExistUnique(_) => {
            VerifyExistFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(
                VerifyExistUniqueFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
        ExistFactFamily::NotExist(_) => {
            VerifyExistFactResult::NotExistFact(VerifyNotExistFactResult::Success(
                VerifyNotExistFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
    }))
}

fn exist_fact_result_failed(fact: &ExistFactFamily, failed: VerifyExistFactFailed) -> VerifyExistFactResult {
    match fact {
        ExistFactFamily::Exist(_) => {
            VerifyExistFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(failed))
        }
        ExistFactFamily::ExistUnique(_) => {
            VerifyExistFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(failed))
        }
        ExistFactFamily::NotExist(_) => {
            VerifyExistFactResult::NotExistFact(VerifyNotExistFactResult::Failed(failed))
        }
    }
}
