use crate::prelude::*;

impl Runtime {
    /// Freeze one assignment-local assumption before its Runtime environment
    /// is popped. The recursive inference Result remains the semantic owner of
    /// every source/conclusion identity; this helper only validates and names
    /// the source FactId for the enclosing assignment Result.
    pub fn freeze_by_assignment_assumption_result(
        &self,
        fact: Fact,
        reason: impl Into<String>,
        mut infers: SuccessInferResult,
    ) -> Result<SuccessVerifyByAssignmentAssumptionResult, RuntimeError> {
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let [store] = infers.store_fact_outputs.as_slice() else {
            return Err(RuntimeError::from(UnknownRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "assignment assumption must retain exactly one source store".to_string(),
                    fact.line_file(),
                    None,
                    vec![],
                ),
            )));
        };
        if store.itself_and_why_itself_is_stored.0.to_string() != fact.to_string() {
            return Err(RuntimeError::from(UnknownRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "assignment assumption store changed its source fact".to_string(),
                    fact.line_file(),
                    None,
                    vec![],
                ),
            )));
        }
        let fact_id = store.fact_id.ok_or_else(|| {
            RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new(
                None,
                "assignment assumption store has no frozen FactId".to_string(),
                fact.line_file(),
                None,
                vec![],
            )))
        })?;
        Ok(SuccessVerifyByAssignmentAssumptionResult {
            fact,
            fact_id,
            reason: reason.into(),
            infers,
        })
    }
}
