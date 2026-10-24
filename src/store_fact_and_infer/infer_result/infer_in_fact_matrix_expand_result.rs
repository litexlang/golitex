use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactMatrixExpandResult {
    pub source_fact_id: FactId,
    pub matrix_space: MatrixSet,
    pub carrier_equal: KnownEqualityPathProof,
    pub derived: Box<StoreInferredFactResult>,
}
