use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactFamilyUnionResult {
    pub derived: Box<StoreInferredFactResult>,
}
