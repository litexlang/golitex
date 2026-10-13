use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{InferDvdDefinitionResult, InferDvdFactResult};

impl Runtime {
    pub(crate) fn infer_dvd_fact(
        &mut self,
        fact: &DvdFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferDvdFactResult>> {
        let derived =
            self.store_builtin_definition_consequences(&AtomicFact::DvdFact(fact.clone()), state)?;
        let [remainder_zero, integer_multiple]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "DvdFact definition must store its two original clauses".into(),
                )
            })?;
        Ok(vec![InferDvdFactResult::Definition(
            InferDvdDefinitionResult {
                source_fact_id: fact.fact_id,
                remainder_zero,
                integer_multiple,
            },
        )])
    }
}
