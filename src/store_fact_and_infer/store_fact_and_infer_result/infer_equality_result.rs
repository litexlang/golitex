use crate::runtime::FactId;

use super::StoreFactAndInferResult;

// One equality-infer rule hit (parallel to EqualitySearchProofBy* arms).
// Unlike verify (stop at first success), every matching arm is kept in the
// parent Vec and its derived facts are stored.
pub enum InferEqualityResult {
    // Rule: `a^x = y` with `a^x $in R+` ⇒ `y $in R+`.
    PositiveRealPower(InferEqualFactPositiveRealPowerResult),
}

pub struct InferEqualFactPositiveRealPowerResult {
    pub derived: Vec<StoreFactAndInferResult>,
}

impl InferEqualityResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
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
