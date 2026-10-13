use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferNotExistDemorganForallResult {
    pub derived: Box<StoreInferredFactResult>,
}
