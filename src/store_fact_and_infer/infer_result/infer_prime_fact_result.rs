use super::InferPrimeDefinitionResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferPrimeFactResult {
    Definition(InferPrimeDefinitionResult),
}

impl InferPrimeFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Definition(p) => vec![&p.lower_bound, &p.trial_divisors],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
