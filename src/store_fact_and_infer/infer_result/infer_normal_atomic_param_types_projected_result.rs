use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferNormalAtomicParamTypesProjectedResult {
    pub derived: Vec<StoreInferredFactResult>,
}
