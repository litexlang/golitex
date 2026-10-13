use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferSurjectiveDefinitionResult {
    pub source_fact_id: FactId,
    pub derived: Vec<StoreInferredFactResult>,
}
