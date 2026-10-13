use super::InferBijectiveDefinitionResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferBijectiveFactResult {
    Definition(InferBijectiveDefinitionResult),
}

impl InferBijectiveFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Definition(p) => vec![&p.injective, &p.surjective],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
