use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferSubsetFiniteUpperBoundResult {
    pub source_fact_id: FactId,
    pub upper_finite_proof: crate::execute::execute_fact_stmt::VerifyFactResult,
    pub derived: Box<StoreInferredFactResult>,
}
