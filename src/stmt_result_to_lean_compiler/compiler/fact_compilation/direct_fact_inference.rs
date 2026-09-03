//! Direct facts and conjunction component inference.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: publish an otherwise-direct fact proof, then consume every
    /// typed inference child from that source FactId in its retained order.
    /// Specialized fact families run before this method; this is the common
    /// path for proof evidence such as a Runtime-resolved numeric comparison
    /// whose ordinary store also owns supported inference Results.
    pub(in super::super) fn compile_direct_fact_with_typed_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let source_fact = result.fact();
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("typed-inference fact changed between verification and store".into());
        }
        let source_fact_id = result
            .store
            .fact_id
            .ok_or_else(|| "typed-inference fact store has no FactId".to_string())?;
        let source_outputs = result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.fact_id == Some(source_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
            })
            .collect::<Vec<_>>();
        let [source_output] = source_outputs.as_slice() else {
            return Err("typed-inference fact must retain one exact source store output".into());
        };
        if source_output.inferred_facts.len() != source_output.inferred_fact_ids.len() {
            return Err("typed-inference fact changed its inferred FactId arity".into());
        }
        let Some(proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(verified)?
        else {
            return Ok(false);
        };
        let native_equality = self
            .construct_lean_native_equality_proof_from_direct_fact_result_using_its_well_definedness(
                verified,
            )?;
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&verified.checked, &source_fact)?;
        }
        let proposition =
            self.render_fact_using_well_definedness_result(&verified.checked, &source_fact)?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact.clone());
        if let Some(native_equality) = native_equality {
            self.retain_native_equality_proof_using_result_well_definedness(
                verified,
                source_fact_id,
                &source_fact,
                native_equality,
            )?;
        }
        self.next_fact_name_index += 1;
        let mut allowed_sources = self
            .install_equality_chain_adjacent_projections_for_typed_inference(
                &source_fact,
                source_fact_id,
                &theorem_name,
                &result.store.infers,
                "typed-inference fact Result",
            )?;
        for source in self.install_numeric_order_chain_adjacent_projections_for_typed_inference(
            &source_fact,
            source_fact_id,
            &theorem_name,
            &result.store.infers,
            "typed-inference fact Result",
        )? {
            if !allowed_sources.iter().any(|existing| {
                existing.0 == source.0 && existing.1.to_string() == source.1.to_string()
            }) {
                allowed_sources.push(source);
            }
        }
        // Inferred conclusions may repeat source objects (notably function
        // applications) whose only recursive certificate lives in the parent
        // fact's WD Result. Keep that exact context active for the complete
        // typed-inference replay, then restore the enclosing scope.
        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&verified.checked)?;
        let parent_well_definedness = self.environment_stack.well_definedness.replace(certificate);
        let inference_compilation = self
            .compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
                &result.store.infers,
                &allowed_sources,
                "typed-inference fact Result",
            );
        self.environment_stack.well_definedness = parent_well_definedness;
        inference_compilation?;
        Ok(true)
    }

    /// `Combine`: publish the proved conjunction once, then bind every exact
    /// inferred component FactId to its structural Lean projection. Later
    /// Results cite those identities through the ordinary compiler stack.
    pub(in super::super) fn compile_direct_conjunction_fact_with_component_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        let source_fact = result.fact();
        let Fact::AndFact(source_conjunction) = &source_fact else {
            return Ok(false);
        };
        if result.store.infers.rule_applications.is_empty()
            || result
                .store
                .infers
                .rule_applications
                .iter()
                .any(|application| {
                    !matches!(application.rule, InferRule::ConjunctionImpliesComponent(_))
                })
        {
            return Ok(false);
        }
        if result.store.fact.to_string() != source_fact.to_string() {
            return Err("conjunction changed between verification and store".into());
        }
        let components = source_conjunction
            .facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>();
        let (source_fact_id, component_fact_ids) =
            validate_conjunction_store_and_component_inference_results(
                &result.store.infers,
                &source_fact,
                &components,
                "conjunction fact store",
            )?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(verified)?
        else {
            return Ok(false);
        };
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        let source_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_theorem_name} : {source_proposition} := by\n  exact {source_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(source_fact_id, source_theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(source_fact_id, source_fact);
        self.next_fact_name_index += 1;

        for (component_index, (component, component_fact_id)) in components
            .iter()
            .zip(component_fact_ids.into_iter())
            .enumerate()
        {
            let projection = conjunction_projection(
                &format!("({source_theorem_name})"),
                component_index,
                components.len(),
            )?;
            self.environment_stack
                .fact_names
                .insert(component_fact_id, projection);
            self.environment_stack
                .fact_propositions
                .insert(component_fact_id, component.clone());
        }
        for (component_index, application) in
            result.store.infers.rule_applications.iter().enumerate()
        {
            let [component] = application.conclusions.as_slice() else {
                return Err(format!(
                    "conjunction component {component_index} lost its nested inference Result"
                ));
            };
            self.compile_defined_predicate_inference_results_in_current_environment(
                &component.infers,
                DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
            )?;
        }
        validate_flattened_inferred_fact_ids_are_visible(
            &result.store.infers,
            &self.environment_stack,
            "conjunction fact store",
        )?;
        Ok(true)
    }

    /// Common `Leaf` / `Wrap` fact publication path. Proof construction reads
    /// the recursive Result directly, while this statement layer owns the
    /// exact store FactId and Lean declaration. Facts with inference children
    /// stay in their dedicated `Combine` paths until those typed infer Results
    /// are migrated.
    pub(in super::super) fn compile_direct_fact_without_inference(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<bool, String> {
        let Some(verified) = result.verification() else {
            return Ok(false);
        };
        // Binder-owning forall Results have a dedicated compiler layer.
        // In particular, Runtime may publish reduced-binder projections when
        // a conclusion omits source parameters; the generic stored-fact path
        // must not consume that structured store shape first.
        if matches!(verified.proof(), SuccessFactProofResult::ForallProof(_)) {
            return Ok(false);
        }
        if fact_result_contains_inferred_facts(result)
            || !result.store.infers.rule_applications.is_empty()
        {
            return Ok(false);
        }
        let Some(proof) = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(verified)
            .map_err(|error| format!("direct fact proof construction: {error}"))?
        else {
            return Ok(false);
        };
        if matches!(result.fact(), Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(&verified.checked, &result.fact())
                .map_err(|error| format!("direct fact WD validation: {error}"))?;
        }
        self.compile_stored_fact_without_inference(result, proof)
            .map_err(|error| format!("direct fact publication: {error}"))?;
        Ok(true)
    }
}
