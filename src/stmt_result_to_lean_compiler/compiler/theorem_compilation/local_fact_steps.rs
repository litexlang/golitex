//! Fact statement local proof steps.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_fact_stmt_result_as_local_proof_step(
        &mut self,
        result: &SuccessFactStmtResult,
        _proof_step_index: usize,
    ) -> Result<Option<String>, String> {
        let verified = result.verification().ok_or_else(|| {
            format!(
                "trusted local fact `{}` has no Lean verification evidence",
                result.fact()
            )
        })?;
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("local fact changed between verification and store".into());
        }
        let fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "local proof-step fact has no frozen FactId".to_string())?;
        if result.store.infers.is_empty() {
            let Some(existing) = self.environment_stack.fact_propositions.get(&fact_id) else {
                return Err("local proof-step reused a FactId outside its compiler scope".into());
            };
            if existing.to_string() != source_fact.to_string() {
                return Err("local proof-step reused a FactId for a different proposition".into());
            }
        } else {
            if result.store.infers.store_fact_outputs.len() != 1
                || result
                    .store
                    .infers
                    .rule_applications
                    .iter()
                    .any(|application| {
                        !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                    })
            {
                return Ok(None);
            }
            let stored = &result.store.infers.store_fact_outputs[0];
            if stored.fact_id != Some(fact_id)
                || stored.itself_and_why_itself_is_stored.0.to_string() != source_fact.to_string()
                || stored.inferred_facts.len() != stored.inferred_fact_ids.len()
            {
                return Err("local proof-step store does not retain its exact FactId".into());
            }
        }
        // The local proposition and its proof must be rendered under the same
        // child-owned WD occurrence map. Restoring the enclosing theorem map
        // between those two operations can select a semantically identical
        // application occurrence belonging to a different proof step.
        let child_certificate =
            self.construct_well_definedness_to_lean_compilation_context(&verified.checked)?;
        let parent_certificate = Some(
            self.environment_stack
                .well_definedness
                .replace(child_certificate),
        );
        let compiled = (|| {
            install_fact_well_definedness_proof_store_results_in_active_environment(
                verified.checked.proof.as_ref(),
                &mut self.environment_stack,
            )?;
            let proof = self.construct_lean_proof_from_direct_fact_result(verified)?;
            let proposition = render_fact(&source_fact, &self.environment_stack)?;
            // Local proof steps are the theorem-body counterpart of ordinary
            // stored facts.  A reviewed equality Result must therefore retain
            // the same native `=` certificate here as it does at top level;
            // later sibling steps may cite this exact FactId for an order
            // rewrite.  Construct and retain it while the child-owned WD
            // certificate is still active, so function applications and
            // exact numeric representatives render from the semantic objects
            // that the verifier actually checked.
            if let Some(native_equality) =
                self.construct_lean_native_equality_proof_from_direct_fact_result(verified)?
            {
                self.retain_native_equality_proof_in_current_environment(
                    fact_id,
                    &source_fact,
                    native_equality,
                )?;
            }
            Ok::<_, String>((proof, proposition))
        })();
        if let Some(parent_certificate) = parent_certificate {
            self.environment_stack.well_definedness = parent_certificate;
        }
        let (Some(proof), proposition) = compiled? else {
            return Ok(None);
        };
        let name = self.next_local_proof_step_base_name();
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact.clone());
        self.environment_stack
            .fact_lean_propositions
            .insert(fact_id, proposition.clone());
        let mut lines = vec![format!(
            "have {name} : {proposition} := by\n  exact {proof}"
        )];
        if !result.store.infers.is_empty() {
            // Inferred conclusions belong to the same source WD tree as the
            // proved chain. Re-enter that exact child-owned WD frame;
            // rendering them under the enclosing theorem frame could lack the
            // required certificate or select a certificate from another
            // proof step.
            let inference_certificate =
                self.construct_well_definedness_to_lean_compilation_context(&verified.checked)?;
            let inference_parent_certificate = Some(
                self.environment_stack
                    .well_definedness
                    .replace(inference_certificate),
            );
            let inference_compilation = (|| {
                let mut allowed_sources = self
                    .install_equality_chain_adjacent_projections_for_typed_inference(
                        &source_fact,
                        fact_id,
                        &name,
                        &result.store.infers,
                        "local proof-step Result",
                    )?;
                for source in self
                    .install_numeric_order_chain_adjacent_projections_for_typed_inference(
                        &source_fact,
                        fact_id,
                        &name,
                        &result.store.infers,
                        "local proof-step Result",
                    )?
                {
                    if !allowed_sources.iter().any(|existing| {
                        existing.0 == source.0 && existing.1.to_string() == source.1.to_string()
                    }) {
                        allowed_sources.push(source);
                    }
                }
                self.compile_typed_inference_results_as_local_have_statements(
                    &result.store.infers,
                    &allowed_sources,
                    &mut lines,
                    "local proof-step Result",
                )?;
                validate_flattened_inferred_fact_ids_are_visible(
                    &result.store.infers,
                    &self.environment_stack,
                    "local proof-step Result",
                )
            })();
            if let Some(parent_certificate) = inference_parent_certificate {
                self.environment_stack.well_definedness = parent_certificate;
            }
            inference_compilation?;
        }
        Ok(Some(lines.join("\n")))
    }
}
