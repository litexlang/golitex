use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferPowerSetMembershipProjectionResult {
    pub source_carrier: crate::ast::obj::Obj,
    pub carrier_equal: crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof,
    pub derived: Box<StoreInferredFactResult>,
}
