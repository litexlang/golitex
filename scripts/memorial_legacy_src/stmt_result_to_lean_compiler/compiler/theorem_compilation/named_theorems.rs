//! Named theorem compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Compile a named theorem through the same forall/ordinary-fact split as
    /// a checked claim, while retaining the theorem's exact source FactId.
    pub(in super::super) fn compile_named_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.name != result.statement.name
            || verification.fact.to_string() != result.statement.fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Err("named theorem Result changed its declaration or proof-step order".into());
        }

        if let Fact::ForallFact(forall_fact) = &verification.fact {
            return self.compile_named_forall_statement_result_to_lean_source(
                NamedForallStatementResultCompilationInput {
                    name: &verification.name,
                    forall_fact,
                    well_definedness: &verification.well_definedness,
                    proof_scope_assumption_infers: &verification.proof_scope.assumption_infers,
                    proof_scope_assumption_components: &verification
                        .proof_scope
                        .assumption_components,
                    proof_steps: &verification.proof_steps,
                    conclusion_checks: verification.conclusion_checks.iter().collect(),
                    outer_environment_effects: Some(&result.common.infers),
                    source_fact_id: Some(result.source_fact_id),
                },
            );
        }

        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.prove_process.len(),
            &verification.fact,
            &verification.well_definedness,
            &verification.proof_scope,
            &verification.proof_steps,
            &verification.conclusion_checks,
        )?
        else {
            return Ok(false);
        };

        if result.common.infers.store_fact_outputs.len() > 1 {
            return Err("ordinary named theorem has more than one outer source store".into());
        }
        if let Some(stored) = result.common.infers.store_fact_outputs.first() {
            if stored.itself_and_why_itself_is_stored.0.to_string()
                != result.statement.fact.to_string()
                || stored.fact_id != Some(result.source_fact_id)
            {
                return Err(
                    "ordinary named theorem outer store changed its fact or exact FactId".into(),
                );
            }
        } else if !result.common.infers.rule_applications.is_empty() {
            return Err(
                "ordinary named theorem retained inference without its source store".into(),
            );
        }

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        let theorem_name = lean_identifier(&verification.name);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(result.source_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(result.source_fact_id, result.statement.fact.clone());
        self.next_fact_name_index += 1;

        let direct_source_keys = result
            .common
            .infers
            .rule_applications
            .iter()
            .filter(|application| {
                infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            .filter_map(|application| {
                application.premises.first().and_then(|premise| {
                    premise
                        .fact_id
                        .map(|fact_id| (fact_id, premise.fact.to_string()))
                })
            })
            .collect::<HashSet<_>>();
        let direct_infers = SuccessInferResult {
            store_fact_outputs: result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .filter(|output| {
                    output.fact_id.is_some_and(|fact_id| {
                        direct_source_keys.contains(&(
                            fact_id,
                            output.itself_and_why_itself_is_stored.0.to_string(),
                        ))
                    })
                })
                .cloned()
                .collect(),
            rule_applications: result
                .common
                .infers
                .rule_applications
                .iter()
                .filter(|application| {
                    infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                })
                .cloned()
                .collect(),
        };
        let source = [(result.source_fact_id, result.statement.fact.clone())];
        self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
            &direct_infers,
            &source,
            "ordinary named theorem direct inference",
        )?;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "ordinary named theorem",
        )?;
        Ok(true)
    }
}
