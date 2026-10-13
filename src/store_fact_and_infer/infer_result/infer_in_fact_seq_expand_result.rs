use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactSeqExpandResult {
    pub derived: Box<StoreInferredFactResult>,
}
