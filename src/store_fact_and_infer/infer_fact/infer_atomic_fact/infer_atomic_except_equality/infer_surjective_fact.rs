use crate::prelude::*;
use crate::store_fact_and_infer::{InferSurjectiveDefinitionResult, InferSurjectiveFactResult};

impl Runtime {
    pub(crate) fn infer_surjective_fact(
        &mut self,
        fact: &SurjectiveFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferSurjectiveFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::SurjectiveFact(fact.clone()),
            state,
        )?;
        Ok(vec![InferSurjectiveFactResult::Definition(
            InferSurjectiveDefinitionResult {
                source_fact_id: fact.fact_id,
                derived,
            },
        )])
    }
}
