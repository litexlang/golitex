use super::InferWeakIntegerLowerBoundInNResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferGreaterEqualFactResult {
    WeakIntegerLowerBoundInN(InferWeakIntegerLowerBoundInNResult),
}

impl InferGreaterEqualFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::WeakIntegerLowerBoundInN(p) => vec![p.derived.as_ref()],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
