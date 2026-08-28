//! Local object and by-definition proof steps.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: a local `let` publishes its symbol and exact defining
    /// equality only in the compiler frame that owns the surrounding proof.
    /// The recursive proof-step consumer therefore needs no separate
    /// local-environment IR and no Runtime lookup.
    pub(in super::super) fn compile_let_obj_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessLetObjStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        if !result.common.infers.rule_applications.is_empty() {
            return Err("local let-object retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("local let-object must retain exactly one defining store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("local let-object defining store retained inferred facts".into());
        }

        let statement = &result.statement;
        let source_name = statement.symbol_binding.name();
        let lean_name = lean_identifier(source_name);
        let rendered_value = render_obj(&statement.value, &self.environment_stack)?;
        let defined_object: Obj =
            Identifier::new_bound(source_name.to_string(), statement.symbol_binding.as_ref())
                .into();
        let defining_equality: Fact = EqualFact::new(
            defined_object,
            statement.value.clone(),
            statement.line_file.clone(),
        )
        .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != defining_equality.to_string() {
            return Err("local let-object Result changed its defining equality".into());
        }
        let defining_equality_fact_id = store
            .fact_id
            .ok_or_else(|| "local let-object defining equality has no FactId".to_string())?;

        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate local compiler symbol identity for `{source_name}`"
            ));
        }
        let rendered_equality = render_fact(&defining_equality, &self.environment_stack)?;
        let theorem_name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, defining_equality.clone());
        self.environment_stack
            .transparent_object_definitions
            .insert(
                statement.symbol_binding.id(),
                CompilerTransparentObjectDefinition {
                    value: statement.value.clone(),
                    defining_equality,
                    defining_equality_fact_id,
                },
            );

        Ok(Some(vec![
            format!("let {lean_name} := {rendered_value}"),
            format!(
                "have {theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ),
        ]))
    }

    /// `Combine`: retain a `by def` statement as one local proof step. The
    /// target FactId becomes visible in the current compiler frame, while an
    /// inferred definition component must either cite an already visible
    /// exact FactId or carry its own recursive component proof.
    pub(in super::super) fn compile_by_definition_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessByDefStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let mut prerequisite_lines = Vec::new();
        if let Some(verification) = &result.verification {
            for (clause_index, check) in verification.clause_checks.iter().enumerate() {
                let check = check.factual_success().ok_or_else(|| {
                    format!("by-definition clause check {clause_index} is not factual")
                })?;
                if matches!(check.proof(), SuccessFactProofResult::ForallProof(_)) {
                    let Some(lines) =
                        self.compile_direct_forall_fact_result_as_local_proof_steps(check)?
                    else {
                        return Err(format!(
                            "by-definition forall clause {clause_index} has no local binder compiler"
                        ));
                    };
                    prerequisite_lines.extend(lines);
                }
            }
        }
        let Some(proof) = self.construct_lean_proof_from_by_definition_stmt_result(result)? else {
            return Ok(None);
        };
        if result
            .common
            .infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Ok(None);
        }
        let [output] = result.common.infers.store_fact_outputs.as_slice() else {
            return Ok(None);
        };
        if output.itself_and_why_itself_is_stored.0.to_string() != proof.target.fact.to_string()
            || output.inferred_facts.len() != output.inferred_fact_ids.len()
        {
            return Err("local by-definition Result changed its target or inferred effects".into());
        }
        let target_fact_id = output
            .fact_id
            .ok_or_else(|| "local by-definition target has no FactId".to_string())?;
        let target_name = format!("__step{proof_step_index}");
        prerequisite_lines.push(format!(
            "have {target_name} : {} := by\n  exact {}",
            proof.target.proposition, proof.target.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(target_fact_id, target_name);
        self.environment_stack
            .fact_propositions
            .insert(target_fact_id, proof.target.fact.clone());
        self.install_compiled_by_definition_component_bindings(&proof.components)?;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "local by-definition Result",
        )?;
        Ok(Some(prerequisite_lines))
    }
}
