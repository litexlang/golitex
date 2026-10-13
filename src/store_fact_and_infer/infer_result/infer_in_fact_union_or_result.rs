use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactUnionOrResult {
    pub derived: Box<StoreInferredFactResult>,
}
