use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactRealIntervalResult {
    pub real_membership: StoreInferredFactResult,
    pub lower_bound: StoreInferredFactResult,
    pub upper_bound: StoreInferredFactResult,
}
