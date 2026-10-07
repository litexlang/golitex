use crate::ast::fact::{AtomicFact, Fact, OrFact};
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProof;
use crate::ast::obj::Obj;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_or_fact::well_defined_result::{
    FailToVerifyOrFactWellDefinedResult, OrFactWellDefinedProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::FactWellDefinedProof;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreFactAndInferResult;

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

// After WD Success: builtin → selected branch (direct or ¬ atomic others) → known_or → known_forall.
pub enum OrFactSearchedProof {
    ByBuiltinRule(OrFactSearchProofByBuiltinRule),
    BySelectedBranch(OrFactSearchProofBySelectedBranch),
    ByKnownOrFact(OrFactSearchProofByKnownOrFact),
    ByKnownForallFact(SearchProofByKnownForallFact),
}

// Or-fact builtin search evidence. One variant per rule.
// Rigid multi-predicate surfaces (trichotomy permutations, fixed `n = 0 or n >= 1`)
// get separate variants. Swap-symmetric binary ors keep one evidence struct; the
// matcher may accept either branch order without a second rule.
pub enum OrFactSearchProofByBuiltinRule {
    // Rigid surface: `a = b or a < b or a > b`.
    // Property: any two reals are comparable by =, <, or >.
    // Example: after `have a, b R`, prove `a = b or a < b or a > b`.
    RealLineTrichotomyEqLessGreater(OrBuiltinRealLineTrichotomyEqLessGreater),
    // Rigid surface: `a < b or a = b or a > b`.
    // Example: after `have a, b R`, prove `a < b or a = b or a > b`.
    RealLineTrichotomyLessEqGreater(OrBuiltinRealLineTrichotomyLessEqGreater),
    // Rigid surface: `a > b or a = b or a < b`.
    // Example: after `have a, b R`, prove `a > b or a = b or a < b`.
    RealLineTrichotomyGreaterEqLess(OrBuiltinRealLineTrichotomyGreaterEqLess),
    // Rigid surface: `n = 0 or n >= 1` for `n $in N`.
    // Property: every natural is zero or at least one.
    // Example: after `have n N`, prove `n = 0 or n >= 1`.
    NaturalZeroOrAtLeastOne(OrBuiltinNaturalZeroOrAtLeastOne),
    // Swap-symmetric binary or: `P or not P` (either branch order).
    // Property: classical excluded middle on a pair of complementary atomic facts.
    // Example: `1 = 1 or 1 != 1`.
    ComplementaryAtomic(OrBuiltinComplementaryAtomic),
    // Swap-symmetric binary or: `abs(x) = x or abs(x) = (-x)` (either branch order).
    // Property: absolute value equals the number or its additive inverse.
    // Example: after `have x R`, prove `abs(x) = x or abs(x) = (-x)`.
    AbsSignSplit(OrBuiltinAbsSignSplit),
    // Swap-symmetric binary or: `a = 0 or b = 0` (either branch order) when
    // `a * b = 0` (or `b * a = 0`) is known.
    // Property: a real product is zero only if a factor is zero.
    // Example: after `have a, b R` and `trust a * b = 0`, prove `a = 0 or b = 0`.
    ZeroProductSplit(OrBuiltinZeroProductSplit),
    // Swap-symmetric binary or: `a < b or a >= b` (either branch order).
    // Property: strict < and weak >= are complementary on R.
    // Example: after `have a, b R`, prove `a < b or a >= b`.
    LessOrGreaterEqual(OrBuiltinLessOrGreaterEqual),
    // Swap-symmetric binary or: `a > b or a <= b` (either branch order).
    // Property: strict > and weak <= are complementary on R.
    // Example: after `have a, b R`, prove `a > b or a <= b`.
    GreaterOrLessEqual(OrBuiltinGreaterOrLessEqual),
    // Swap-symmetric binary or: `a <= b or a >= b` (either branch order).
    // Property: weak order on R is total (comparability).
    // Example: after `have a, b R`, prove `a <= b or a >= b`.
    WeakOrderLeOrGe(OrBuiltinWeakOrderLeOrGe),
    // Swap-symmetric / dual surfaces for one rule: `a = b or a < b` when `a <= b`
    // is known (dual: `a = b or a > b` when `a >= b` is known).
    // Property: equality plus the matching strict order covers a known weak bound.
    // Example: after `have a, b R` and `trust a <= b`, prove `a = b or a < b`.
    EqualityPlusStrictCoversWeak(OrBuiltinEqualityPlusStrictCoversWeak),
    // Exhaustive residues: `n % m = 0 or … or n % m = m-1` for positive literal m.
    // Property: every integer has a unique residue mod a positive integer.
    // Example: after `have n Z`, prove `n % 2 = 0 or n % 2 = 1`.
    CompleteResidues(OrBuiltinCompleteResidues),
    // Finite successor equalities plus strict tail from a known integer lower bound.
    // Property: if `x >= base` in Z, then x equals one of finitely many successors or exceeds the last.
    // Example: after `have x Z` and `trust x >= 1`, prove `x = 1 or x = 2 or x = 3 or x > 3`.
    IntegerSuccessorTail(OrBuiltinIntegerSuccessorTail),
    // Swap-symmetric binary or: `a != 0 or b != 0` (either branch order) from known
    // `a^2 + b^2 != 0` (or `a*a + b*b`).
    // Property: a nonzero square sum forces a nonzero component.
    // Example: after `have a, b R` and `trust a^2 + b^2 != 0`, prove `a != 0 or b != 0`.
    SquareSumComponentNonzero(OrBuiltinSquareSumComponentNonzero),
    // Packaging `not A or B` (exactly one negative-polarity branch): assume A, prove B.
    // Property: classical implication as a two-branch disjunction.
    // Example: after `trust forall x R: $p(x) =>: $q(x)` and `have a R`,
    // prove `not $p(a) or $q(a)`.
    ClassicalImplication(OrBuiltinClassicalImplication),
    // Swap-symmetric / dual surfaces for one rule: `x <= n or x >= n + 1`
    // (either branch order; predecessor dual also matches).
    // Property: consecutive integers leave no gap on Z.
    // Example: after `have x, n Z`, prove `x <= n or x >= n + 1`.
    IntegerDiscreteSplit(OrBuiltinIntegerDiscreteSplit),
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

// Evidence for swap-symmetric `P or not P` (matcher accepts either branch order).
pub struct OrBuiltinComplementaryAtomic {
    pub left: AtomicFact,
    pub right: AtomicFact,
}

// Evidence for swap-symmetric `abs(x) = x or abs(x) = (-x)`.
pub struct OrBuiltinAbsSignSplit {
    pub arg: Obj,
}

// Evidence for swap-symmetric `a = 0 or b = 0` after `a, b $in R` and known `a * b = 0`.
pub struct OrBuiltinZeroProductSplit {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
    pub product_zero: VerifyFactResult,
}

// Evidence for swap-symmetric `a < b or a >= b` after both sides in R.
pub struct OrBuiltinLessOrGreaterEqual {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for swap-symmetric `a > b or a <= b` after both sides in R.
pub struct OrBuiltinGreaterOrLessEqual {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for swap-symmetric `a <= b or a >= b` after both sides in R.
pub struct OrBuiltinWeakOrderLeOrGe {
    pub left: Obj,
    pub right: Obj,
    pub left_in_r: VerifyFactResult,
    pub right_in_r: VerifyFactResult,
}

// Evidence for equality-plus-strict covering a known weak bound.
pub struct OrBuiltinEqualityPlusStrictCoversWeak {
    pub left: Obj,
    pub right: Obj,
    pub weak_bound: VerifyFactResult,
}

// Evidence for exhaustive residues mod a positive literal modulus.
pub struct OrBuiltinCompleteResidues {
    pub subject: Obj,
    pub modulus: Obj,
}

// Evidence for integer successor-tail split after Z membership and lower bound.
pub struct OrBuiltinIntegerSuccessorTail {
    pub subject: Obj,
    pub base: Obj,
    pub subject_in_z: VerifyFactResult,
    pub base_in_z: VerifyFactResult,
    pub subject_ge_base: VerifyFactResult,
}

// Evidence for component nonzero from a known nonzero square sum.
pub struct OrBuiltinSquareSumComponentNonzero {
    pub left: Obj,
    pub right: Obj,
    pub square_sum_nonzero: VerifyFactResult,
}

// Evidence for classical `not A or B`: assume A locally, prove B.
pub struct OrBuiltinClassicalImplication {
    pub assumed_from_branch_index: usize,
    pub conclusion_branch_index: usize,
    pub assumed_premise: Fact,
    pub assumed_well_defined: FactWellDefinedProof,
    pub assumed_store_and_infer: StoreFactAndInferResult,
    pub conclusion_proof: VerifyFactResult,
    pub local_env: Box<ExecEnv>,
}

// Evidence for integer discrete split after both sides in Z.
pub struct OrBuiltinIntegerDiscreteSplit {
    pub subject: Obj,
    pub base: Obj,
    pub subject_in_z: VerifyFactResult,
    pub base_in_z: VerifyFactResult,
}

// Prove selected locally, directly or assuming ¬ of every other atomic branch.
// Direct Or introduction has an empty assumed_negated_branches list.
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
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<EqualFactSearchedProof>,
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
