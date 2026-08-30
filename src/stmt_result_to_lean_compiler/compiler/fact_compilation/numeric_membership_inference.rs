//! Standard numeric membership inference compilation and installation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Direct `Leaf + Combine` compilation for a closed expression proved to
    /// belong to one standard numeric carrier. The recursive evaluation,
    /// source store identity, and every typed carrier inference are consumed
    /// from `SuccessFactStmtResult` without constructing backend fact IR.
    pub(in super::super) fn compile_closed_standard_numeric_membership_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) = builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if !builtin.subgoals.is_empty() {
            return Err("closed standard numeric membership gained proof subgoals".into());
        }

        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string()
            || evidence.expected_target.to_string() != source_fact.to_string()
        {
            return Err(
                "closed standard numeric membership changed between verification, proof, and store"
                    .into(),
            );
        }
        let Fact::AtomicFact(AtomicFact::InFact(membership)) = &source_fact else {
            return Err(
                "closed standard numeric membership retained a non-membership target".into(),
            );
        };
        if !matches!(&membership.set, Obj::StandardSet(set) if *set == evidence.target_set)
            || obj_equality_key(&membership.element)
                != obj_equality_key(&evidence.evaluation.expression)
        {
            return Err(
                "closed standard numeric membership changed its expression or target carrier"
                    .into(),
            );
        }

        validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        validate_success_evaluate_obj_result(&evidence.evaluation)?;

        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored closed numeric membership has no FactId".to_string())?;
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let proof = render_closed_numeric_membership_from_result(
            &source_fact,
            evidence.target_set,
            &evidence.evaluation,
            &self.environment_stack,
        )?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        self.next_fact_name_index += 1;

        self.compile_standard_numeric_membership_infer_result_as_top_level_declarations(
            &source_fact,
            source_fact_id,
            &result.store.infers,
            "closed standard numeric membership inference",
        )?;
        Ok(true)
    }

    pub(in super::super) fn compile_natural_membership_infer_result(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let applications = infers
            .rule_applications
            .iter()
            .filter(|application| {
                application.rule == InferRule::NaturalMembershipImpliesNonnegative
                    && application.premises.len() == 1
                    && application.premises[0].fact_id == Some(source_fact_id)
                    && application.premises[0].fact.to_string() == source_fact.to_string()
            })
            .collect::<Vec<_>>();
        if applications.len() != 1 {
            return Err(format!(
                "natural membership expected one typed nonnegative inference for its exact FactId, retained {}",
                applications.len()
            ));
        }
        let application = applications[0];
        if application.conclusions.len() != 1 {
            return Err("natural-membership inference must retain one conclusion".into());
        }
        let conclusion = &application.conclusions[0];
        let conclusion_fact_id = conclusion
            .fact_id
            .ok_or_else(|| "natural-membership inference conclusion has no FactId".to_string())?;
        let conclusion_retains_its_store =
            conclusion.infers.store_fact_outputs.iter().any(|output| {
                output.fact_id == Some(conclusion_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == conclusion.fact.to_string()
            });
        if !conclusion_retains_its_store {
            return Err("natural-membership inference conclusion lost its store layer".into());
        }
        let output_retains_conclusion = infers.store_fact_outputs.iter().any(|output| {
            output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    fact.to_string() == conclusion.fact.to_string()
                        && *fact_id == Some(conclusion_fact_id)
                })
                || (output.itself_and_why_itself_is_stored.0.to_string()
                    == conclusion.fact.to_string()
                    && output.fact_id == Some(conclusion_fact_id))
        });
        if !output_retains_conclusion {
            return Err(
                "typed natural-membership inference and ordered store effects disagree".into(),
            );
        }

        let source_theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .ok_or_else(|| "stored source FactId is unavailable to its inference".to_string())?
            .clone();
        let conclusion_proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
        let conclusion_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {conclusion_theorem_name} : {conclusion_proposition} := by\n  exact Litex.Rules.nonnegativeOfInN ({source_theorem_name})"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, conclusion_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.fact.clone());
        self.next_fact_name_index += 1;
        Ok(())
    }

    /// Publish typed standard-numeric inference children as top-level Lean
    /// theorems. The shared compiler first returns each conclusion as one
    /// structured local proof step; this wrapper renders earlier steps as the
    /// local closure of later proofs and publishes the current step under its
    /// exact retained FactId.
    pub(in super::super) fn compile_standard_numeric_membership_infer_result_as_top_level_declarations(
        &mut self,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
        result_layer: &str,
    ) -> Result<(), String> {
        self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
            infers,
            &[(source_fact_id, source_fact.clone())],
            result_layer,
        )
    }

    /// Validate the same typed inference Result as the proof-block route, but
    /// retain each conclusion as a direct Lean proof expression. Function and
    /// matrix constructors have no surrounding tactic block in which to emit
    /// a local `have`; their inherited compiler frame still owns the exact
    /// inferred FactIds and drops them when the Result-owned body is left.
    pub(in super::super) fn install_standard_numeric_membership_inference_results_in_current_environment(
        &mut self,
        infers: &SuccessInferResult,
        allowed_sources: &[(FactId, Fact)],
        result_layer: &str,
    ) -> Result<(), String> {
        let _compiled_steps = self
            .compile_typed_inference_results_in_current_compiler_environment(
                infers,
                allowed_sources,
                CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression,
                result_layer,
                None,
            )?;
        Ok(())
    }
}
