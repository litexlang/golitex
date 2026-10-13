use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{InferBijectiveDefinitionResult, InferBijectiveFactResult};

impl Runtime {
    pub(crate) fn infer_bijective_fact(
        &mut self,
        fact: &BijectiveFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferBijectiveFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::BijectiveFact(fact.clone()),
            state,
        )?;
        let [injective, surjective]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "BijectiveFact definition must store its two original clauses".into(),
                )
            })?;
        Ok(vec![InferBijectiveFactResult::Definition(
            InferBijectiveDefinitionResult {
                source_fact_id: fact.fact_id,
                injective,
                surjective,
            },
        )])
    }
}
