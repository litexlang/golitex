use crate::prelude::*;
use crate::store_fact_and_infer::*;
use crate::store_fact_and_infer::{InferPrimeDefinitionResult, InferPrimeFactResult};

impl Runtime {
    pub(crate) fn infer_prime_fact(
        &mut self,
        fact: &PrimeFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferPrimeFactResult>> {
        let derived = self
            .store_builtin_definition_consequences(&AtomicFact::PrimeFact(fact.clone()), state)?;
        let [lower_bound, trial_divisors]: [StoreInferredFactResult; 2] =
            derived.try_into().map_err(|_| {
                RuntimeError::InternalBug(
                    "prime definition must store its bound and trial-divisor universal".into(),
                )
            })?;
        Ok(vec![InferPrimeFactResult::Definition(
            InferPrimeDefinitionResult {
                source_fact_id: fact.fact_id,
                lower_bound,
                trial_divisors,
            },
        )])
    }
}
