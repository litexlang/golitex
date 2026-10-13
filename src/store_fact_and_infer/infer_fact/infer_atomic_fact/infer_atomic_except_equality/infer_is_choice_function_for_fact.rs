use crate::prelude::*;
use crate::store_fact_and_infer::{
    InferChoiceFunctionDefinitionResult, InferIsChoiceFunctionForFactResult,
};

impl Runtime {
    pub(crate) fn infer_is_choice_function_for_fact(
        &mut self,
        fact: &IsChoiceFunctionForFact,
        state: VerifyState,
    ) -> RuntimeResult<Vec<InferIsChoiceFunctionForFactResult>> {
        let derived = self.store_builtin_definition_consequences(
            &AtomicFact::IsChoiceFunctionForFact(fact.clone()),
            state,
        )?;
        Ok(vec![InferIsChoiceFunctionForFactResult::Definition(
            InferChoiceFunctionDefinitionResult {
                source_fact_id: fact.fact_id,
                derived,
            },
        )])
    }
}
