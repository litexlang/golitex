use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferProperSupersetDefinitionResult {
    pub source_fact_id: FactId,
    pub reverse_subset: StoreInferredFactResult,
    pub distinct: StoreInferredFactResult,
}
