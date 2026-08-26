//! Execution for statements that explicitly choose a verifier operation.
mod antisymmetric_prop_by_stmt;
mod axiom_of_choice_by_stmt;
mod cases_by_stmt;
mod closed_range_by_stmt;
mod contra_by_stmt;
mod definition_by_stmt;
mod enumerate_by_stmt;
mod enumerate_range_by_stmt;
mod extension_by_stmt;
mod finite_set_induc_by_stmt;
mod for_by_stmt;
mod helpers_by_stmt;
mod induc_by_stmt;
mod reflexive_prop_by_stmt;
mod regularity_axiom_by_stmt;
mod struct_definition_by_stmt;
mod symmetric_prop_by_stmt;
mod theorem_application;
mod transitive_prop_by_stmt;
mod zorn_lemma_by_stmt;

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
