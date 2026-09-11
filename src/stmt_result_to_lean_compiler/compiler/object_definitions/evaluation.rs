//! Evaluation statement compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Wrap`: a checked numeric `eval` publishes the evaluator-owned
    /// equality under the exact FactId assigned by its store layer. Runtime
    /// algorithms without a recursive computation Result remain fail-closed.
    pub(in super::super) fn compile_eval_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessEvalStmtResult,
    ) -> Result<(), String> {
        match &result.execution {
            SuccessEvalStmtExecutionResult::SkippedByTrustedExecution => {
                if !result.common.infers.is_empty() {
                    return Err("trusted `eval` unexpectedly published effects".into());
                }
                return Ok(());
            }
            SuccessEvalStmtExecutionResult::Evaluated(execution) => {
                if obj_equality_key(&execution.source_object)
                    != obj_equality_key(&result.statement.obj_to_eval)
                {
                    return Err("eval execution changed its source object".into());
                }
                let evaluation = execution
                    .recursive_numeric_evaluation
                    .as_ref()
                    .ok_or_else(|| {
                        "StmtResultToLeanCompiler cannot compile an eval runtime algorithm without a recursive computation Result"
                            .to_string()
                    })?;
                validate_success_evaluate_obj_result(evaluation)?;
                if obj_equality_key(&evaluation.expression)
                    != obj_equality_key(&execution.source_object)
                    || obj_equality_key(&Obj::Number(evaluation.value.clone()))
                        != obj_equality_key(&execution.evaluated_object)
                {
                    return Err("eval recursive computation changed its input or output".into());
                }
            }
        }

        if !result.common.infers.rule_applications.is_empty() {
            return Err("numeric eval retained unexpected typed inference applications".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("numeric eval must retain exactly one equality store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("numeric eval equality retained unexpected inferred consequences".into());
        }
        let SuccessEvalStmtExecutionResult::Evaluated(execution) = &result.execution else {
            unreachable!("trusted eval returned before store validation")
        };
        let expected_equality: Fact = self
            .runtime
            .new_equal_fact(
                execution.source_object.clone(),
                execution.evaluated_object.clone(),
                result.statement.line_file.clone(),
            )
            .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != expected_equality.to_string() {
            return Err("numeric eval store changed its evaluated equality".into());
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| "numeric eval equality store has no FactId".to_string())?;
        let proposition = render_fact(&expected_equality, &self.environment_stack)?;
        render_obj(&execution.source_object, &self.environment_stack)?;
        render_obj(&execution.evaluated_object, &self.environment_stack)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, expected_equality);
        self.next_fact_name_index += 1;
        Ok(())
    }
}
