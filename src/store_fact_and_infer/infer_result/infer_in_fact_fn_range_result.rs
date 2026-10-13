use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactFnRangeResult {
    pub codomain_membership: StoreInferredFactResult,
    pub preimage_witness: Option<StoreInferredFactResult>,
}
