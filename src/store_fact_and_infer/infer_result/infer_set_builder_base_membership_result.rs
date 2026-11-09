use crate::store_fact_and_infer::{InferInFactResult, StoreInferredFactResult};

pub struct InferSetBuilderBaseMembershipResult {
    pub stored: StoreInferredFactResult,
    pub inferences: Vec<InferInFactResult>,
}

impl InferSetBuilderBaseMembershipResult {
    pub fn new(stored: StoreInferredFactResult, inferences: Vec<InferInFactResult>) -> Self {
        Self { stored, inferences }
    }
}
