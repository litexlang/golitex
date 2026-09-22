use crate::new_pipeline::ast::fact::{ExistShapedFact, Fact};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_shaped_fact::well_defined_result::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::FactId;

// Mirrors ExistShapedFact: plain exist / exist! / not exist are separate owners.
pub enum VerifyExistShapedFactResult {
    PlainExistFact(VerifyPlainExistFactResult),
    ExistUniqueFact(VerifyExistUniqueFactResult),
    NotExistFact(VerifyNotExistFactResult),
}

impl VerifyExistShapedFactResult {
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
    Failed(VerifyExistShapedFactFailed),
}

pub enum VerifyExistUniqueFactResult {
    Success(VerifyExistUniqueFactSuccess),
    Failed(VerifyExistShapedFactFailed),
}

pub enum VerifyNotExistFactResult {
    Success(VerifyNotExistFactSuccess),
    Failed(VerifyExistShapedFactFailed),
}

pub struct VerifyPlainExistFactSuccess {
    pub fact: ExistShapedFact,
    pub well_defined_proof: ExistShapedFactWellDefinedProof,
    pub searched_proof: ExistShapedFactSearchedProof,
}

pub struct VerifyExistUniqueFactSuccess {
    pub fact: ExistShapedFact,
    pub well_defined_proof: ExistShapedFactWellDefinedProof,
    pub searched_proof: ExistShapedFactSearchedProof,
}

pub struct VerifyNotExistFactSuccess {
    pub fact: ExistShapedFact,
    pub well_defined_proof: ExistShapedFactWellDefinedProof,
    pub searched_proof: ExistShapedFactSearchedProof,
}

// Shared fail payload for plain / unique / not-exist (same WD + search stages).
pub enum VerifyExistShapedFactFailed {
    FailToVerifyWellDefined(FailToVerifyExistShapedFactWellDefinedResult),
    FailToSearchProof {
        fact: ExistShapedFact,
        well_defined_proof: ExistShapedFactWellDefinedProof,
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
pub enum ExistShapedFactSearchedProof {
    ByBuiltinRule(ExistShapedFactSearchProofByBuiltinRule),
    ByKnownExistShapedFact(ExistShapedFactSearchProofByKnownExistShapedFact),
    ByKnownForallFact(SearchProofByKnownForallFact),
}

// One exist-builtin rule ↔ one dedicated evidence struct.
pub enum ExistShapedFactSearchProofByBuiltinRule {
    RealLineComparisonWitness(ExistShapedBuiltinRealLineComparisonWitness),
}

// Existential witness on the real line for a comparison atom.
// Mathematical property: for any known real `c`, there exist reals above,
// below, equal to, and distinct from `c`; also there exist pairs `a, b R`
// satisfying any of the six order/equality comparisons.
//
// Examples:
// - `exist x R st {x > 100}` after proving `100 $in R`
// - `exist a, b R st {a > b}` (no free operands)
pub struct ExistShapedBuiltinRealLineComparisonWitness {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct ExistShapedFactSearchProofByKnownExistShapedFact {
    pub cite_fact_id: FactId,
}

// Wrap plain / unique / not-exist into VerifyFactResult::ExistShapedFact(...).

pub fn exist_shaped_fact_result_from_wd_fail(
    fact: &ExistShapedFact,
    reason: FailToVerifyExistShapedFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::ExistShapedFact(Box::new(exist_shaped_fact_result_failed(
        fact,
        VerifyExistShapedFactFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn exist_shaped_fact_result_from_search_fail(
    fact: &ExistShapedFact,
    well_defined_proof: ExistShapedFactWellDefinedProof,
) -> VerifyFactResult {
    VerifyFactResult::ExistShapedFact(Box::new(exist_shaped_fact_result_failed(
        fact,
        VerifyExistShapedFactFailed::FailToSearchProof {
            fact: fact.clone(),
            well_defined_proof,
        },
    )))
}

pub fn exist_shaped_fact_result_from_success(
    fact: &ExistShapedFact,
    well_defined_proof: ExistShapedFactWellDefinedProof,
    searched_proof: ExistShapedFactSearchedProof,
) -> VerifyFactResult {
    VerifyFactResult::ExistShapedFact(Box::new(match fact {
        ExistShapedFact::Exist(_) => {
            VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Success(
                VerifyPlainExistFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
        ExistShapedFact::ExistUnique(_) => {
            VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Success(
                VerifyExistUniqueFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
        ExistShapedFact::NotExist(_) => {
            VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Success(
                VerifyNotExistFactSuccess {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                },
            ))
        }
    }))
}

fn exist_shaped_fact_result_failed(fact: &ExistShapedFact, failed: VerifyExistShapedFactFailed) -> VerifyExistShapedFactResult {
    match fact {
        ExistShapedFact::Exist(_) => {
            VerifyExistShapedFactResult::PlainExistFact(VerifyPlainExistFactResult::Failed(failed))
        }
        ExistShapedFact::ExistUnique(_) => {
            VerifyExistShapedFactResult::ExistUniqueFact(VerifyExistUniqueFactResult::Failed(failed))
        }
        ExistShapedFact::NotExist(_) => {
            VerifyExistShapedFactResult::NotExistFact(VerifyNotExistFactResult::Failed(failed))
        }
    }
}
