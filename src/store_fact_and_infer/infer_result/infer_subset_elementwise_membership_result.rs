use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferSubsetElementwiseMembershipResult {
    pub derived: Box<StoreInferredFactResult>,
}
