use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferBijectiveDefinitionResult {
    pub source_fact_id: FactId,
    pub injective: StoreInferredFactResult,
    pub surjective: StoreInferredFactResult,
}
