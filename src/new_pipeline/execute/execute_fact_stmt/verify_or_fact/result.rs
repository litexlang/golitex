use crate::new_pipeline::ast::fact::{Fact, OrFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_or_fact::well_defined_result::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::new_pipeline::runtime::FactId;
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

pub enum VerifyOrFactResult {
    Success(VerifyOrFactSuccess),
    Failed(VerifyOrFactFailed),
}

pub struct VerifyOrFactSuccess {
    pub fact: OrFact,
    pub well_defined_proof: OrFactWellDefinedProof,
    pub searched_proof: OrFactSearchedProof,
}

pub enum VerifyOrFactFailed {
    FailToVerifyWellDefined(FailToVerifyOrFactWellDefinedResult),
    FailToSearchProof {
        fact: OrFact,
        well_defined_proof: OrFactWellDefinedProof,
    },
}

impl VerifyOrFactResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

// After WD Success: builtin → selected branch (¬ others) → known_or → known_forall.
pub enum OrFactSearchedProof {
    ByBuiltinRule(OrFactSearchProofByBuiltinRule),
    BySelectedBranch(OrFactSearchProofBySelectedBranch),
    ByKnownOrFact(OrFactSearchProofByKnownOrFact),
    ByKnownForallFact(SearchProofByKnownForallFact),
}

// Or-fact builtin search evidence. One variant per rule (branch order is rigid).
pub enum OrFactSearchProofByBuiltinRule {
    // Exact order: `a = b or a < b or a > b`.
    // Property: any two reals are comparable by =, <, or >.
    // Example: have a R, b R => a = b or a < b or a > b
    RealLineTrichotomyEqLessGreater(OrBuiltinRealLineTrichotomyEqLessGreater),
    // Exact order: `a < b or a = b or a > b`.
    // Example: have a R, b R => a < b or a = b or a > b
    RealLineTrichotomyLessEqGreater(OrBuiltinRealLineTrichotomyLessEqGreater),
    // Exact order: `a > b or a = b or a < b`.
    // Example: have a R, b R => a > b or a = b or a < b
    RealLineTrichotomyGreaterEqLess(OrBuiltinRealLineTrichotomyGreaterEqLess),
    // Exact order: `n = 0 or n >= 1` for `n $in N`.
    // Property: every natural is zero or at least one.
    // Example: have n N => n = 0 or n >= 1
    NaturalZeroOrAtLeastOne(OrBuiltinNaturalZeroOrAtLeastOne),
}

// Evidence for `a = b or a < b or a > b` after proving both sides in R.
pub struct OrBuiltinRealLineTrichotomyEqLessGreater {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for `a < b or a = b or a > b` after proving both sides in R.
pub struct OrBuiltinRealLineTrichotomyLessEqGreater {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for `a > b or a = b or a < b` after proving both sides in R.
pub struct OrBuiltinRealLineTrichotomyGreaterEqLess {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for `n = 0 or n >= 1` after proving `n $in N`.
pub struct OrBuiltinNaturalZeroOrAtLeastOne {
    pub n: Obj,
    pub n_in_n: VerifyFactResult,
}

// Classical: assume ¬ of every other branch in a local env, prove selected.
// Example: assume `not (1 = 2)`, prove `1 = 1` ⇒ `1 = 1 or 1 = 2`.
pub struct OrFactSearchProofBySelectedBranch {
    pub selected_index: usize,
    pub assumed_negated_branches: Vec<AssumeNegatedOrBranchResult>,
    pub selected_branch: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

pub struct AssumeNegatedOrBranchResult {
    pub branch_index: usize,
    pub negated_fact: Fact,
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
}

pub struct OrFactSearchProofByKnownOrFact {
    pub cite_fact_id: FactId,
}

pub fn or_fact_result_from_wd_fail(
    reason: FailToVerifyOrFactWellDefinedResult,
) -> VerifyFactResult {
    VerifyFactResult::OrFact(Box::new(VerifyOrFactResult::Failed(
        VerifyOrFactFailed::FailToVerifyWellDefined(reason),
    )))
}

pub fn or_fact_result_from_search_fail(
    fact: &OrFact,
    well_defined_proof: OrFactWellDefinedProof,
) -> VerifyFactResult {
    VerifyFactResult::OrFact(Box::new(VerifyOrFactResult::Failed(
        VerifyOrFactFailed::FailToSearchProof {
            fact: fact.clone(),
            well_defined_proof,
        },
    )))
}

pub fn or_fact_result_from_success(
    fact: &OrFact,
    well_defined_proof: OrFactWellDefinedProof,
    searched_proof: OrFactSearchedProof,
) -> VerifyFactResult {
    VerifyFactResult::OrFact(Box::new(VerifyOrFactResult::Success(VerifyOrFactSuccess {
        fact: fact.clone(),
        well_defined_proof,
        searched_proof,
    })))
}
