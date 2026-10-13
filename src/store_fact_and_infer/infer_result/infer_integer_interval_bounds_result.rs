use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferIntegerIntervalBoundsResult {
    pub integer_membership: StoreInferredFactResult,
    pub lower_bound: StoreInferredFactResult,
    pub upper_bound: StoreInferredFactResult,
    pub positive_membership: Option<StoreInferredFactResult>,
    pub singleton_equality: Option<StoreInferredFactResult>,
}

impl InferIntegerIntervalBoundsResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        [
            &self.integer_membership,
            &self.lower_bound,
            &self.upper_bound,
        ]
        .into_iter()
        .chain(self.positive_membership.iter())
        .chain(self.singleton_equality.iter())
        .collect()
    }
}
