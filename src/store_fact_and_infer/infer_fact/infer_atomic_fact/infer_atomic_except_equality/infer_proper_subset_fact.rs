use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{InferProperSubsetDefinitionResult, InferProperSubsetFactResult};

impl Runtime {
    pub(crate) fn infer_proper_subset_fact(
        &mut self,
        fact: &ProperSubsetFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferProperSubsetFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::ProperSubsetFact(fact.clone()),
            state,
        )?;
        let [subset, distinct]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "ProperSubsetFact definition must store its two original clauses".into(),
                )
            })?;
        Ok(vec![InferProperSubsetFactResult::Definition(
            InferProperSubsetDefinitionResult {
                source_fact_id: fact.fact_id,
                subset,
                distinct,
            },
        )])
    }
}
