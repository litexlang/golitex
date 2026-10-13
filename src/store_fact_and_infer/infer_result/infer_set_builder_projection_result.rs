use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferSetBuilderProjectionResult {
    BaseMembership(StoreInferredFactResult),
    Condition {
        /// Zero-based index in the selected builder's original conditions.
        condition_index: usize,
        stored: StoreInferredFactResult,
    },
}

impl InferSetBuilderProjectionResult {
    pub fn stored(&self) -> &StoreInferredFactResult {
        match self {
            Self::BaseMembership(s) => s,
            Self::Condition { stored, .. } => stored,
        }
    }
    pub fn stored_mut(&mut self) -> &mut StoreInferredFactResult {
        match self {
            Self::BaseMembership(s) => s,
            Self::Condition { stored, .. } => stored,
        }
    }
}
