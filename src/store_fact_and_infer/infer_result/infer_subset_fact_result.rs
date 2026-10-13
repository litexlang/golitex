use super::{InferSubsetElementwiseMembershipResult, InferSubsetFiniteUpperBoundResult};
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferSubsetFactResult {
    ElementwiseMembership(InferSubsetElementwiseMembershipResult),
    FiniteUpperBound(InferSubsetFiniteUpperBoundResult),
}

impl InferSubsetFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::ElementwiseMembership(p) => vec![p.derived.as_ref()],
            Self::FiniteUpperBound(p) => vec![p.derived.as_ref()],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
