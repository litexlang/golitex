use super::InferPreimageConstructionResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactPreimageSetResult {
    pub source_fact_id: FactId,
    pub source_equal: KnownEqualityPathProof,
    pub construction: InferPreimageConstructionResult,
    pub derived: Vec<StoreInferredFactResult>,
}
