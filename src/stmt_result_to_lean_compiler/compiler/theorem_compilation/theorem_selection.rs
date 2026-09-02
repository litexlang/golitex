//! By-theorem selection compilation and proof construction.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: replay one theorem application in a child compiler scope,
    /// prove the selected atomic consequence from those exact temporary
    /// FactIds, and publish only the parent store owned by `by thm`.
    pub(in super::super) fn compile_by_theorem_selection_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<bool, String> {
        let Some(body) = self.construct_lean_proof_from_by_theorem_selection_stmt_result(result)?
        else {
            return Ok(false);
        };
        if let Some(visible) = self
            .environment_stack
            .fact_propositions
            .get(&body.retained_fact_id)
        {
            if visible.to_string() != body.fact.to_string() {
                return Err("by-thm reused FactId changed its selected proposition".into());
            }
            return Ok(true);
        }
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(body.retained_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(body.retained_fact_id, body.fact);
        self.next_fact_name_index += 1;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "by-thm selected parent fact",
        )?;
        Ok(true)
    }

    pub(in super::super) fn construct_lean_proof_from_by_theorem_selection_stmt_result(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<Option<CompiledByTheoremSelectionProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.selected_fact.to_string() != result.statement.selected_fact.to_string() {
            return Err("by-thm Result changed its selected fact".into());
        }
        let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
            verification.temporary_application.as_ref()
        else {
            return Err("by-thm Result did not retain a temporary release-thm statement".into());
        };
        if application.statement.name().to_string() != result.statement.name().to_string()
            || application.statement.args().len() != result.statement.args().len()
            || application
                .statement
                .args()
                .iter()
                .zip(result.statement.args().iter())
                .any(|(actual, expected)| obj_equality_key(actual) != obj_equality_key(expected))
        {
            return Err("by-thm temporary application changed its theorem or arguments".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let Some(mut proof_lines) = self
                .compile_stmt_result_as_local_proof_steps(&verification.temporary_application, 1)?
            else {
                return Ok(None);
            };
            let selected_check = verification
                .selected_fact_check
                .verified()
                .ok_or_else(|| "by-thm selected-fact check is not factual".to_string())?;
            let selected_fact: Fact = verification.selected_fact.clone().into();
            if selected_check.fact().to_string() != selected_fact.to_string() {
                return Err("by-thm selected-fact check changed its target".into());
            }
            let Some(selected_proof) =
                self.construct_lean_proof_from_direct_fact_result(selected_check)?
            else {
                return Ok(None);
            };
            proof_lines.push(format!("exact {selected_proof}"));
            let proposition = render_fact(&selected_fact, &self.environment_stack)?;
            let retained_fact_id = if result.common.infers.is_empty() {
                let SuccessFactProofResult::StoredFactCitation(citation) = selected_check.proof()
                else {
                    return Err(
                        "by-thm reused selected fact has no exact citation evidence".into(),
                    );
                };
                let fact_id = citation.source_fact_id;
                let visible = self
                    .environment_stack
                    .fact_propositions
                    .get(&fact_id)
                    .ok_or_else(|| format!("by-thm selected FactId `{fact_id}` is not visible"))?;
                if visible.to_string() != selected_fact.to_string() {
                    return Err("by-thm selected FactId changed its proposition".into());
                }
                fact_id
            } else if result.common.infers.rule_applications.is_empty() {
                validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &selected_fact,
                    "by-thm selected parent fact",
                )?
            } else {
                validate_defined_predicate_fact_publication_effects(
                    &result.common.infers,
                    &selected_fact,
                    "by-thm selected parent fact",
                )?
            };
            Ok(Some(CompiledByTheoremSelectionProofBody {
                fact: selected_fact,
                retained_fact_id,
                proposition,
                proof_lines,
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }
}
