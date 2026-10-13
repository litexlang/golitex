use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactIndexIntersectResult {
    pub ambient_membership: StoreInferredFactResult,
    pub fiber_membership: Option<StoreInferredFactResult>,
}
