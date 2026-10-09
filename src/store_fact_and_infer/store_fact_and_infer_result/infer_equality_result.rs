use crate::prelude::*;
use crate::runtime::FactId;

use super::StoreFactAndInferResult;

// One equality-infer rule hit (parallel to EqualitySearchProofBy* arms).
// Unlike verify (stop at first success), every matching arm is kept in the
// parent Vec and its derived facts are stored.
pub enum InferEqualityResult {
    AdditiveCancellation(InferEqualFactAdditiveCancellationResult),
    NonzeroFactorCancellation(InferEqualFactNonzeroFactorCancellationResult),
    SubtractiveCancellation(InferEqualFactSubtractiveCancellationResult),
    CommonDenominatorCancellation(InferEqualFactCommonDenominatorCancellationResult),
    NonzeroNumeratorCancellation(InferEqualFactNonzeroNumeratorCancellationResult),
    // Rule: `a^x = y` with `a^x $in R+` ⇒ `y $in R+`.
    PositiveRealPower(InferEqualFactPositiveRealPowerResult),
}

pub struct InferEqualFactAdditiveCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferEqualFactAdditiveCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        derived: StoreFactAndInferResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            derived: Box::new(derived),
        }
    }
}

pub struct InferEqualFactNonzeroFactorCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub factor_nonzero_proof: VerifyFactResult,
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferEqualFactNonzeroFactorCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        factor_nonzero_proof: VerifyFactResult,
        derived: StoreFactAndInferResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            factor_nonzero_proof,
            derived: Box::new(derived),
        }
    }
}

pub struct InferEqualFactPositiveRealPowerResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferEqualFactSubtractiveCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferEqualFactSubtractiveCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        derived: StoreFactAndInferResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            derived: Box::new(derived),
        }
    }
}

pub struct InferEqualFactCommonDenominatorCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub denominator_nonzero_proof: VerifyFactResult,
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferEqualFactCommonDenominatorCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        denominator_nonzero_proof: VerifyFactResult,
        derived: StoreFactAndInferResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            denominator_nonzero_proof,
            derived: Box::new(derived),
        }
    }
}

pub struct InferEqualFactNonzeroNumeratorCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub numerator_nonzero_proof: VerifyFactResult,
    pub left_denominator_nonzero_proof: VerifyFactResult,
    pub right_denominator_nonzero_proof: VerifyFactResult,
    pub derived: Box<StoreFactAndInferResult>,
}

impl InferEqualFactNonzeroNumeratorCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        numerator_nonzero_proof: VerifyFactResult,
        left_denominator_nonzero_proof: VerifyFactResult,
        right_denominator_nonzero_proof: VerifyFactResult,
        derived: StoreFactAndInferResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            numerator_nonzero_proof,
            left_denominator_nonzero_proof,
            right_denominator_nonzero_proof,
            derived: Box::new(derived),
        }
    }
}

impl InferEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::AdditiveCancellation(r) => r.derived.stored_fact_ids(),
            Self::NonzeroFactorCancellation(r) => r.derived.stored_fact_ids(),
            Self::SubtractiveCancellation(r) => r.derived.stored_fact_ids(),
            Self::CommonDenominatorCancellation(r) => r.derived.stored_fact_ids(),
            Self::NonzeroNumeratorCancellation(r) => r.derived.stored_fact_ids(),
            Self::PositiveRealPower(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
        }
    }
}
