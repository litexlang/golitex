use super::InferCoprimeDefinitionResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferCoprimeFactResult {
    Definition(InferCoprimeDefinitionResult),
}

impl InferCoprimeFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::Definition(p) => vec![&p.not_both_zero, &p.gcd_one],
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
