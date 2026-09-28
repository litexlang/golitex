use crate::ast::fact::{ExistShapedFact, Fact};
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::well_defined_result::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::runtime::FactId;

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
    // Witness by a known member: `a $in S` ⇒ `exist x S st {x = a}` (or `a = x`).
    EqualityWitnessFromMembership(ExistShapedBuiltinEqualityWitnessFromMembership),
    // Witness from nonempty: `$is_nonempty_set(S)` ⇒ `exist x S st {x $in S}`.
    NonemptySetMemberWitness(ExistShapedBuiltinNonemptySetMemberWitness),
    // Rational with positive integer denominator: `q $in Q` ⇒
    // `exist a, b Z st {b > 0, q = a / b}`.
    RationalPositiveDenominator(ExistShapedBuiltinRationalPositiveDenominator),
    // Rational as integer / nonzero-integer: `q $in Q` ⇒
    // `exist a Z, b Z* st {q = a / b}`.
    RationalIntegerRatio(ExistShapedBuiltinRationalIntegerRatio),
    // Zero remainder ⇒ integer multiple: `a % b = 0`, `b != 0` ⇒
    // `exist k Z st {a = b * k}`.
    IntegerMultipleFromZeroRemainder(ExistShapedBuiltinIntegerMultipleFromZeroRemainder),
    // Archimedean reciprocal: `epsilon $in R+` ⇒ `exist n N+ st {1 / n < epsilon}`.
    ArchimedeanReciprocal(ExistShapedBuiltinArchimedeanReciprocal),
    // Real density by midpoint: `a < b` on reals ⇒ `exist r R st {a < r < b}`.
    RealDensityMidpoint(ExistShapedBuiltinRealDensityMidpoint),
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

// Equality witness from membership.
// Mathematical property: if `a $in S`, then `exist x S st {x = a}` (and `a = x`).
// Example: known `2 $in {1, 2}` proves `exist x {1, 2} st {x = 2}`.
pub struct ExistShapedBuiltinEqualityWitnessFromMembership {
    pub membership_proof: VerifyFactResult,
}

// Nonempty-set member witness.
// Mathematical property: `$is_nonempty_set(S)` ⇒ `exist x S st {x $in S}`.
// Example: `$is_nonempty_set({1})` proves `exist x {1} st {x $in {1}}`.
pub struct ExistShapedBuiltinNonemptySetMemberWitness {
    pub nonempty_proof: VerifyFactResult,
}

// Rational representation with a positive integer denominator.
// Mathematical property: every rational is `a / b` for integers `a, b` with `b > 0`.
// Example: `1/2 $in Q` proves `exist a, b Z st {b > 0, 1/2 = a / b}`
// (when exist-body WD of the quotient succeeds).
pub struct ExistShapedBuiltinRationalPositiveDenominator {
    pub rational_membership_proof: VerifyFactResult,
}

// Rational as an integer numerator over a nonzero integer denominator.
// Mathematical property: every rational is `a / b` for `a Z`, `b Z*`.
// Example: `1/2 $in Q` proves `exist a Z, b Z* st {1/2 = a / b}`.
pub struct ExistShapedBuiltinRationalIntegerRatio {
    pub rational_membership_proof: VerifyFactResult,
}

// Integer multiple from a zero Euclidean remainder.
// Mathematical property: if `a, b $in Z`, `b != 0`, and `a % b = 0`, then
// there is an integer `k` with `a = b * k`.
// Example: known `6 % 3 = 0` proves `exist k Z st {6 = 3 * k}`.
pub struct ExistShapedBuiltinIntegerMultipleFromZeroRemainder {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

// Archimedean reciprocal bound.
// Mathematical property: every positive real `ε` admits `n N+` with `1/n < ε`.
// Example: `0.5 $in R+` proves `exist n N+ st {1 / n < 0.5}`.
pub struct ExistShapedBuiltinArchimedeanReciprocal {
    pub positive_bound_proof: VerifyFactResult,
}

// Real density via the midpoint principle.
// Mathematical property: if `a < b` for reals `a, b`, then some real lies
// strictly between them (e.g. the midpoint).
// Example: known `0 < 1` proves `exist r R st {0 < r < 1}`.
pub struct ExistShapedBuiltinRealDensityMidpoint {
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
