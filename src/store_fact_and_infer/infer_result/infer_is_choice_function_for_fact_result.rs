use super::InferChoiceFunctionDefinitionResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferIsChoiceFunctionForFactResult {
    Definition(InferChoiceFunctionDefinitionResult),
}

impl InferIsChoiceFunctionForFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Definition(p) => p.derived.iter().collect(),
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
