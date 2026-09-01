//! Claim compilation and local universal claim steps.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: compile each retained proof-step Result inside one inherited
    /// compiler environment, then wrap the retained conclusion proof in the
    /// persistent theorem introduced by `claim`.
    pub(in super::super) fn compile_claim_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessClaimStmtResult,
    ) -> Result<bool, String> {
        let Some(well_definedness) = &result.well_definedness else {
            return Ok(false);
        };
        if let Fact::ForallFact(forall_fact) = &result.statement.fact {
            if result.proof_steps.len() != result.statement.proof.len() {
                return Err(
                    "forall `claim` Result changed its statement or proof-step order".into(),
                );
            }
            let claim_name = format!("__fact{}", self.next_fact_name_index);
            return self.compile_named_forall_statement_result_to_lean_source(
                NamedForallStatementResultCompilationInput {
                    name: &claim_name,
                    forall_fact,
                    well_definedness,
                    proof_scope_assumption_infers: &result.domain.assumption_infers,
                    proof_scope_assumption_components: &result.domain.assumption_components,
                    proof_steps: &result.proof_steps,
                    conclusion_checks: result.conclusion_checks.iter().collect(),
                    outer_environment_effects: Some(&result.environment_effects),
                },
            );
        }
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            &result.statement.fact,
            well_definedness,
            &result.domain,
            &result.proof_steps,
            &result.conclusion_checks,
        )?
        else {
            return Ok(false);
        };

        if !result.environment_effects.rule_applications.is_empty()
            || result.environment_effects.store_fact_outputs.len() != 1
        {
            return Err("ordinary `claim` must retain exactly one outer store effect".into());
        }
        let stored = &result.environment_effects.store_fact_outputs[0];
        if stored.itself_and_why_itself_is_stored.0.to_string() != result.statement.fact.to_string()
            || !stored.inferred_facts.is_empty()
            || !stored.inferred_fact_ids.is_empty()
        {
            return Err("ordinary `claim` outer store changed its target or inferred facts".into());
        }
        let fact_id = stored
            .fact_id
            .ok_or_else(|| "ordinary `claim` outer store has no FactId".to_string())?;

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, result.statement.fact.clone());
        self.next_fact_name_index += 1;
        Ok(true)
    }

    pub(in super::super) fn compile_forall_claim_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessClaimStmtResult,
        _proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let Some(well_definedness) = &result.well_definedness else {
            return Ok(None);
        };
        let Fact::ForallFact(forall_fact) = &result.statement.fact else {
            return Ok(None);
        };
        if result.proof_steps.len() != result.statement.proof.len() {
            return Err(
                "local forall `claim` Result changed its statement or proof-step order".into(),
            );
        }

        let claim_name = self.next_local_proof_step_base_name();
        let declaration_count = self.declarations.len();
        let compiled = self.compile_named_forall_statement_result_to_lean_source(
            NamedForallStatementResultCompilationInput {
                name: &claim_name,
                forall_fact,
                well_definedness,
                proof_scope_assumption_infers: &result.domain.assumption_infers,
                proof_scope_assumption_components: &result.domain.assumption_components,
                proof_steps: &result.proof_steps,
                conclusion_checks: result.conclusion_checks.iter().collect(),
                outer_environment_effects: Some(&result.environment_effects),
            },
        )?;
        if !compiled {
            return Ok(None);
        }
        if self.declarations.len() != declaration_count + 1 {
            return Err("local forall `claim` did not emit exactly one declaration".into());
        }
        let declaration = self
            .declarations
            .pop()
            .ok_or_else(|| "local forall `claim` lost its generated declaration".to_string())?;
        let theorem_prefix = format!("theorem {claim_name} :");
        let local_prefix = format!("have {claim_name} :");
        let local_declaration = declaration
            .strip_prefix(&theorem_prefix)
            .map(|body| format!("{local_prefix}{body}"))
            .ok_or_else(|| {
                "local forall `claim` generated an unexpected declaration shape".to_string()
            })?;
        Ok(Some(vec![local_declaration]))
    }

    /// Compile an ordinary local `claim` as one scoped Lean `have`.  Its
    /// nested proof steps are checked by the same Result consumer used for a
    /// top-level claim, while only the claim's frozen outer FactId is
    /// published to the surrounding theorem frame.
    pub(in super::super) fn compile_fact_claim_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessClaimStmtResult,
        _proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let Some(well_definedness) = &result.well_definedness else {
            return Ok(None);
        };
        if matches!(&result.statement.fact, Fact::ForallFact(_)) {
            return Ok(None);
        }
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            &result.statement.fact,
            well_definedness,
            &result.domain,
            &result.proof_steps,
            &result.conclusion_checks,
        )?
        else {
            return Ok(None);
        };
        if !result.environment_effects.rule_applications.is_empty()
            || result.environment_effects.store_fact_outputs.len() != 1
        {
            return Err("local ordinary `claim` must retain one outer store effect".into());
        }
        let stored = &result.environment_effects.store_fact_outputs[0];
        if stored.itself_and_why_itself_is_stored.0.to_string() != result.statement.fact.to_string()
            || !stored.inferred_facts.is_empty()
            || !stored.inferred_fact_ids.is_empty()
        {
            return Err(
                "local ordinary `claim` outer store changed its target or inferences".into(),
            );
        }
        let fact_id = stored
            .fact_id
            .ok_or_else(|| "local ordinary `claim` outer store has no FactId".to_string())?;
        let name = self.next_local_proof_step_base_name();
        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, result.statement.fact.clone());
        Ok(Some(vec![format!(
            "have {name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        )]))
    }
}
