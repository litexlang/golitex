//! Stored fact compilation and exact citations.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_stored_fact_without_inference(
        &mut self,
        result: &SuccessFactStmtResult,
        proof: String,
    ) -> Result<(), String> {
        let source_fact = result.fact();
        // A reviewed equality rule can own both the heterogeneous Litex.Same
        // theorem published below and an exact native `=` certificate used by
        // later order/equality transports. Previously this certificate was
        // retained only for equality steps nested inside combined proofs, so
        // an ordinary standalone normalization fact could be cited by FactId
        // but not used as a native rewrite. Construct it from the same Result
        // before publication, then bind it to the statement's exact FactId.
        let native_equality =
            self.construct_lean_native_equality_proof_from_direct_fact_result(result)?;
        // Most facts render solely from the compiler environment. Function
        // applications are the remaining target-side exception: their exact
        // application term still reads the temporary WD rendering view. Only
        // construct that view if ordinary Result-driven rendering says it is
        // needed, then restore the surrounding compiler layer on every path.
        let proposition = match render_fact(&source_fact, &self.environment_stack) {
            Ok(proposition) => proposition,
            Err(initial_render_error)
                if matches!(source_fact, Fact::AtomicFact(_) | Fact::ForallFact(_)) =>
            {
                self.render_fact_using_well_definedness_result(
                    &result.well_definedness,
                    &source_fact,
                )
                .map_err(|wd_render_error| {
                    format!(
                        "{initial_render_error}; Result-owned WD rendering also failed: {wd_render_error}"
                    )
                })?
            }
            Err(error) => return Err(error),
        };
        self.compile_stored_fact_without_inference_with_pre_rendered_proposition(
            result,
            proof,
            proposition,
        )?;
        if let Some(native_equality) = native_equality {
            let fact_id = result
                .store
                .fact_id
                .ok_or_else(|| "stored equality fact has no FactId".to_string())?;
            self.retain_native_equality_proof_in_current_environment(
                fact_id,
                &source_fact,
                native_equality,
            )?;
        }
        Ok(())
    }

    /// Publish a fact whose proposition was rendered by the Result-owned
    /// child environment before that environment was popped. Forall/function
    /// telescopes need this path because re-rendering their type in the parent
    /// would discard exact local FactId bindings.
    pub(in super::super) fn compile_stored_fact_without_inference_with_pre_rendered_proposition(
        &mut self,
        result: &SuccessFactStmtResult,
        proof: String,
        proposition: String,
    ) -> Result<(), String> {
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("fact changed between verification and store".into());
        }
        let fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "stored fact has no FactId".to_string())?;
        if !result.store.infers.rule_applications.is_empty() {
            return Err("zero-inference fact retained unexpected typed infer rules".into());
        }
        match result.store.infers.store_fact_outputs.as_slice() {
            [store]
                if store.fact_id == Some(fact_id)
                    && store.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
                    && store.inferred_facts.is_empty()
                    && store.inferred_fact_ids.is_empty() => {}
            [] if self
                .environment_stack
                .fact_propositions
                .get(&fact_id)
                .is_some_and(|stored| {
                    stored.to_string() == source_fact.to_string()
                        || equality_facts_are_equal_up_to_nested_binder_alpha(stored, &source_fact)
                }) => {}
            _ => {
                let installed = self
                    .environment_stack
                    .fact_propositions
                    .get(&fact_id)
                    .map(ToString::to_string);
                return Err(format!(
                    "zero-inference fact store output disagrees with the statement store: FactId `{fact_id}`, statement `{source_fact}`, store outputs {}, installed proposition {:?}",
                    result.store.infers.store_fact_outputs.len(),
                    installed,
                ));
            }
        }
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        let declaration = if matches!(source_fact, Fact::ForallFact(_)) {
            format!("theorem {theorem_name} :\n    {proposition} := {proof}")
        } else {
            format!("theorem {theorem_name} : {proposition} := by\n  exact {proof}")
        };
        self.declarations.push(declaration);
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact);
        self.environment_stack
            .fact_lean_propositions
            .insert(fact_id, proposition);
        self.next_fact_name_index += 1;
        Ok(())
    }

    pub(in super::super) fn compile_exact_fact_citation_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let SuccessFactProofResult::StoredFactCitation(citation) = result.proof() else {
            return Ok(false);
        };
        let source_fact_id = citation.source_fact_id;
        if fact_result_contains_inferred_facts(result) {
            return Ok(false);
        }
        let source_fact = result.fact();
        // FactId is the citation identity. `resolve_fact_citation` additionally
        // checks that the retained proposition is unchanged, including
        // alpha-equivalent forall binders, before exposing its Lean name.
        let proof = resolve_fact_citation(
            &source_fact_id,
            &citation.source_fact,
            &self.environment_stack,
        )?;
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&result.well_definedness, &source_fact)?;
        }
        self.compile_stored_fact_without_inference(result, proof)?;
        Ok(true)
    }
}
