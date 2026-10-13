use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferCoprimeDefinitionResult {
    pub source_fact_id: FactId,
    pub not_both_zero: StoreInferredFactResult,
    pub gcd_one: StoreInferredFactResult,
}
