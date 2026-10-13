use crate::prelude::*;
use crate::store_fact_and_infer::{InferInjectiveDefinitionResult, InferInjectiveFactResult};

impl Runtime {
    pub(crate) fn infer_injective_fact(
        &mut self,
        fact: &InjectiveFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferInjectiveFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::InjectiveFact(fact.clone()),
            state,
        )?;
        Ok(vec![InferInjectiveFactResult::Definition(
            InferInjectiveDefinitionResult {
                source_fact_id: fact.fact_id,
                derived,
            },
        )])
    }
}
