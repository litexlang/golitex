use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferNotForallFactResult {
    pub derived_exist: Box<StoreInferredFactResult>,
}
