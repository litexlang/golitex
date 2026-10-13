use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactIntersectBothResult {
    pub left_membership: StoreInferredFactResult,
    pub right_membership: StoreInferredFactResult,
}
