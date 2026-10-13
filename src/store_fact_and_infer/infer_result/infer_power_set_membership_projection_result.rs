use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferPowerSetMembershipProjectionResult {
    pub derived: Box<StoreInferredFactResult>,
}
