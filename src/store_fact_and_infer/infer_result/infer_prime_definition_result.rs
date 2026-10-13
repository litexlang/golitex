use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferPrimeDefinitionResult {
    pub source_fact_id: FactId,
    pub lower_bound: StoreInferredFactResult,
    pub trial_divisors: StoreInferredFactResult,
}
