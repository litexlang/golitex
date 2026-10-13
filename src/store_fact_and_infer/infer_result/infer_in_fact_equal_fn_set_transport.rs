use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactEqualFnSetTransport {
    pub membership_fact_id: FactId,
    pub carrier_equal: KnownEqualityPathProof,
    pub derived: StoreInferredFactResult,
}
