use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferProperSubsetDefinitionResult {
    pub source_fact_id: FactId,
    pub subset: StoreInferredFactResult,
    pub distinct: StoreInferredFactResult,
}
