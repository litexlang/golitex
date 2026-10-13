use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferSupersetElementwiseMembershipResult {
    pub derived: Box<StoreInferredFactResult>,
}
