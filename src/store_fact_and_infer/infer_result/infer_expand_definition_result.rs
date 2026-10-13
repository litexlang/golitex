use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferExpandDefinitionResult {
    pub derived: Vec<StoreInferredFactResult>,
}
