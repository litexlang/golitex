use super::InferProperSupersetDefinitionResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferProperSupersetFactResult {
    Definition(InferProperSupersetDefinitionResult),
}

impl InferProperSupersetFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Definition(p) => vec![&p.reverse_subset, &p.distinct],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
