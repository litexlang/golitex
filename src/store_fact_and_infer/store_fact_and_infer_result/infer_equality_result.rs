use crate::runtime::FactId;

use super::StoreFactAndInferResult;

// One equality-infer rule hit (parallel to EqualitySearchProofBy* arms).
// Unlike verify (stop at first success), every matching arm is kept in the
// parent Vec and its derived facts are stored.
pub enum InferEqualityResult {
    // Rule: equality to literal cart/tuple records shape facts on the other side.
    CartTupleShape(InferEqualFactCartTupleShapeResult),
    // Rule: `a^x = y` with `a^x $in R+` ⇒ `y $in R+`.
    PositiveRealPower(InferEqualFactPositiveRealPowerResult),
    // Rule: simple linear equality records the unique closed solved value.
    // Example: store `x + 4 = 2` ⇒ also store `x = -2`.
    SimpleLinearSolvedValue(InferEqualFactSimpleLinearSolvedValueResult),
}

pub struct InferEqualFactCartTupleShapeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferEqualFactPositiveRealPowerResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferEqualFactSimpleLinearSolvedValueResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

impl InferEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::CartTupleShape(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::PositiveRealPower(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
            Self::SimpleLinearSolvedValue(r) => {
                let mut ids = Vec::new();
                for d in &r.derived {
                    ids.extend(d.stored_fact_ids());
                }
                ids
            }
        }
    }
}
