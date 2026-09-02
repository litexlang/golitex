//! Registered predicate property compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: compile the exact forall proof owned by a successful
    /// `by reflexive_prop`/`symmetric_prop`/`transitive_prop`/
    /// `antisymmetric_prop` Result, then remember the generated theorem only
    /// in the active compiler environment. The registration is not a stored
    /// Litex fact, so it deliberately has no fabricated FactId.
    pub(in super::super) fn compile_registered_predicate_property_stmt_result_to_lean_source(
        &mut self,
        statement_forall_fact: &ForallFact,
        statement_proof_step_count: usize,
        common: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyByPropRegistrationResult>,
        compilation_kind: RegisteredPredicatePropertyCompilationKind,
    ) -> Result<(), String> {
        let verification = verification.ok_or_else(|| {
            format!(
                "{} predicate-property registration has no recursive verification Result",
                compilation_kind.result_name()
            )
        })?;
        if verification.registration_type != compilation_kind.result_name()
            || verification.forall_fact.to_string() != statement_forall_fact.to_string()
            || verification.proof_steps.len() != statement_proof_step_count
            || verification.prop_name.is_empty()
        {
            return Err(format!(
                "{} predicate-property registration changed its declaration or proof-step order",
                compilation_kind.result_name()
            ));
        }
        if !common.infers.store_fact_outputs.is_empty()
            || !common.infers.rule_applications.is_empty()
        {
            return Err(format!(
                "{} predicate-property registration unexpectedly published fact effects",
                compilation_kind.result_name()
            ));
        }

        let theorem_name = format!(
            "__litex_registered_{}_{}_{}",
            compilation_kind.result_name(),
            lean_identifier(&verification.prop_name),
            self.next_fact_name_index
        );
        let forall_check = verification.forall_check.verified().ok_or_else(|| {
            format!(
                "{} predicate-property registration retained a non-factual forall check",
                compilation_kind.result_name()
            )
        })?;
        if forall_check.fact().to_string() != verification.forall_fact.to_string() {
            return Err(format!(
                "{} predicate-property registration changed its checked forall fact",
                compilation_kind.result_name()
            ));
        }
        let SuccessFactProofResult::ForallProof(forall_proof) = forall_check.proof() else {
            return Err(format!(
                "{} predicate-property registration did not retain the verify_forall_fact Result layer",
                compilation_kind.result_name()
            ));
        };
        if forall_proof.forall_fact.to_string() != verification.forall_fact.to_string()
            || forall_proof.proves.len() != verification.forall_fact.then_facts.len()
        {
            return Err(format!(
                "{} predicate-property registration changed its recursive forall proof structure",
                compilation_kind.result_name()
            ));
        }
        if forall_proof
            .assumption_infers
            .rule_applications
            .iter()
            .chain(verification.assumption_infers.rule_applications.iter())
            .any(|application| !defined_predicate_infer_rule(&application.rule))
            || !success_infer_results_have_same_semantic_structure(
                &forall_proof.assumption_infers,
                &verification.assumption_infers,
            )
        {
            return Err(format!(
                "{} predicate-property registration changed its local assumption effects",
                compilation_kind.result_name()
            ));
        }
        for (nested, registration) in forall_proof
            .assumption_infers
            .store_fact_outputs
            .iter()
            .zip(verification.assumption_infers.store_fact_outputs.iter())
        {
            if nested.fact_id != registration.fact_id
                || nested.itself_and_why_itself_is_stored.0.to_string()
                    != registration.itself_and_why_itself_is_stored.0.to_string()
                || nested.itself_and_why_itself_is_stored.1
                    != registration.itself_and_why_itself_is_stored.1
                || nested.inferred_facts.len() != registration.inferred_facts.len()
                || nested.inferred_fact_ids != registration.inferred_fact_ids
                || nested
                    .inferred_facts
                    .iter()
                    .zip(registration.inferred_facts.iter())
                    .any(|(left, right)| left.to_string() != right.to_string())
            {
                return Err(format!(
                    "{} predicate-property registration changed a local assumption effect",
                    compilation_kind.result_name()
                ));
            }
        }
        let mut conclusion_checks = Vec::with_capacity(forall_proof.proves.len());
        for (conclusion_index, (proved, expected)) in forall_proof
            .proves
            .iter()
            .zip(verification.forall_fact.then_facts.iter())
            .enumerate()
        {
            if proved.stmt.clone().to_fact().to_string() != expected.clone().to_fact().to_string() {
                return Err(format!(
                    "{} predicate-property registration changed recursive conclusion {conclusion_index}",
                    compilation_kind.result_name()
                ));
            }
            conclusion_checks.push(proved.result.as_ref());
        }
        let compiled = self.compile_named_forall_statement_result_to_lean_source(
            NamedForallStatementResultCompilationInput {
                name: &theorem_name,
                forall_fact: &verification.forall_fact,
                well_definedness: &forall_check.checked,
                proof_scope_assumption_infers: &verification.assumption_infers,
                proof_scope_assumption_components: &[],
                proof_steps: &verification.proof_steps,
                conclusion_checks,
                outer_environment_effects: None,
                source_fact_id: None,
            },
        )?;
        if !compiled {
            return Err(format!(
                "StmtResultToLeanCompiler does not support this {} predicate-property proof Result shape",
                compilation_kind.result_name()
            ));
        }

        let binding = RegisteredPredicatePropertyTheoremBinding {
            theorem_name,
            forall_fact: verification.forall_fact.clone(),
        };
        match compilation_kind {
            RegisteredPredicatePropertyCompilationKind::Reflexive => {
                self.environment_stack
                    .registered_reflexive_predicate_theorem_bindings
                    .insert(verification.prop_name.clone(), binding);
            }
            RegisteredPredicatePropertyCompilationKind::Symmetric => {
                self.environment_stack
                    .registered_symmetric_predicate_theorem_bindings
                    .entry(verification.prop_name.clone())
                    .or_default()
                    .push(binding);
            }
            RegisteredPredicatePropertyCompilationKind::Transitive => {
                self.environment_stack
                    .registered_transitive_predicate_theorem_bindings
                    .insert(verification.prop_name.clone(), binding);
            }
            RegisteredPredicatePropertyCompilationKind::Antisymmetric => {
                self.environment_stack
                    .registered_antisymmetric_predicate_theorem_bindings
                    .insert(verification.prop_name.clone(), binding);
            }
        }
        Ok(())
    }
}
