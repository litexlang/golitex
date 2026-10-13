use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactListSetOrEqualitiesResult {
    pub derived: Box<StoreInferredFactResult>,
}
