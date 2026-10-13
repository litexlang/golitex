use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{
    InferProperSupersetDefinitionResult, InferProperSupersetFactResult,
};

impl Runtime {
    pub(crate) fn infer_proper_superset_fact(
        &mut self,
        fact: &ProperSupersetFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferProperSupersetFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::ProperSupersetFact(fact.clone()),
            state,
        )?;
        let [reverse_subset, distinct]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "ProperSupersetFact definition must store its two original clauses".into(),
                )
            })?;
        Ok(vec![InferProperSupersetFactResult::Definition(
            InferProperSupersetDefinitionResult {
                source_fact_id: fact.fact_id,
                reverse_subset,
                distinct,
            },
        )])
    }
}
