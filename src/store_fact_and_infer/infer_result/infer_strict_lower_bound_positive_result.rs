use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferStrictLowerBoundPositiveResult {
    pub source_fact_id: FactId,
    pub bound_nonnegative_proof: crate::execute::execute_fact_stmt::VerifyFactResult,
    pub derived: Box<StoreInferredFactResult>,
}
