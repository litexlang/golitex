use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactSetMinusSplitResult {
    pub base_membership: StoreInferredFactResult,
    pub excluded_membership: StoreInferredFactResult,
    pub singleton_inequality: Option<StoreInferredFactResult>,
}
