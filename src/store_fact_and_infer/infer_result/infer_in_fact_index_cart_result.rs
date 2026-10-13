use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactIndexCartResult {
    pub function_membership: StoreInferredFactResult,
    pub choice_certificate: StoreInferredFactResult,
}
