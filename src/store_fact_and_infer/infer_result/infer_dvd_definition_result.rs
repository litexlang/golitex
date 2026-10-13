use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferDvdDefinitionResult {
    pub source_fact_id: FactId,
    pub remainder_zero: StoreInferredFactResult,
    pub integer_multiple: StoreInferredFactResult,
}
