use crate::prelude::*;
use crate::store_fact_and_infer::StoreInferredFactResult;
use crate::store_fact_and_infer::{InferCoprimeDefinitionResult, InferCoprimeFactResult};

impl Runtime {
    pub(crate) fn infer_coprime_fact(
        &mut self,
        fact: &CoprimeFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferCoprimeFactResult>> {
        let derived = self
            .store_builtin_definition_consequences(&AtomicFact::CoprimeFact(fact.clone()), state)?;
        let [not_both_zero, gcd_one]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "CoprimeFact definition must store its two original clauses".into(),
                )
            })?;
        Ok(vec![InferCoprimeFactResult::Definition(
            InferCoprimeDefinitionResult {
                source_fact_id: fact.fact_id,
                not_both_zero,
                gcd_one,
            },
        )])
    }
}
