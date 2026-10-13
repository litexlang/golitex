use super::{InferExpandDefinitionResult, InferNormalAtomicParamTypesProjectedResult};
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferNormalAtomicFactResult {
    ParamTypes(InferNormalAtomicParamTypesProjectedResult),
    ExpandDefinition(InferExpandDefinitionResult),
}

impl InferNormalAtomicFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::ParamTypes(p) => p.derived.iter().collect(),
            Self::ExpandDefinition(p) => p.derived.iter().collect(),
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
