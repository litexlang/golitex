use crate::new_pipeline::runtime::FactId;

use super::StoreFactAndInferResult;

// One equality-infer rule hit (parallel to EqualitySearchProofBy* arms).
// Unlike verify (stop at first success), every matching arm is kept in the
// parent Vec and its derived facts are stored.
pub enum InferEqualityResult {
    // Rule: equality to literal cart/tuple records shape facts on the other side.
    CartTupleShape(InferEqualFactCartTupleShapeResult),
    // Rule: `0 = u - v` or `u - v = 0` ⇒ `u = v`.
    SubtractionEqualsZero(InferEqualFactSubtractionEqualsZeroResult),
}

pub struct InferEqualFactCartTupleShapeResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

pub struct InferEqualFactSubtractionEqualsZeroResult {
    pub derived: Box<StoreFactAndInferResult>,
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
            Self::SubtractionEqualsZero(r) => r.derived.stored_fact_ids(),
        }
    }
}
