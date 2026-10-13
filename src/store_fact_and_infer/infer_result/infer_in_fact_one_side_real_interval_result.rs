use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactOneSideRealIntervalResult {
    pub real_membership: StoreInferredFactResult,
    pub bound: StoreInferredFactResult,
}
