//! Trust statements, facts accepted with trust, and source axioms.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_trust_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTrustStmtResult,
    ) -> Result<bool, String> {
        if result.statement.facts.is_empty() {
            return Err("explicit source `trust` retained no propositions".into());
        }
        if result.common.infers.store_fact_outputs.len() != result.statement.facts.len()
            || result
                .common
                .infers
                .rule_applications
                .iter()
                .any(|application| !defined_predicate_infer_rule(&application.rule))
            || result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .any(|store| store.inferred_facts.len() != store.inferred_fact_ids.len())
        {
            return Ok(false);
        }
        for (fact, store) in result
            .statement
            .facts
            .iter()
            .zip(result.common.infers.store_fact_outputs.iter())
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != fact.to_string() {
                return Err("trusted fact order changed between statement and store Result".into());
            }
            let fact_id = store
                .fact_id
                .ok_or_else(|| "trusted source fact has no FactId".to_string())?;
            let proposition = match fact {
                Fact::ForallFact(forall) => {
                    render_forall_fact_type(forall, &self.environment_stack)?
                }
                _ => render_fact(fact, &self.environment_stack)?,
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations
                .push(format!("axiom {theorem_name} : {proposition}"));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "explicit source trust",
        )?;
        Ok(true)
    }

    /// `Combine`: declare each explicitly trusted object in source order,
    /// publish its exact parameter-membership FactId, then publish the
    /// statement's attached trusted facts. This direct slice accepts ordinary
    /// object carriers whose stores have no inferred siblings. Refined/set
    /// bindings and typed infer children remain separate migration routes.
    pub(in super::super) fn compile_trust_have_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessTrustHaveStmtResult,
    ) -> Result<bool, String> {
        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.iter().any(|store| {
                !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty()
            })
        {
            return Ok(false);
        }

        let mut parameters = Vec::new();
        for group in &result.statement.param_def.groups {
            let ParamType::Obj(carrier) = &group.param_type else {
                return Ok(false);
            };
            if matches!(
                carrier,
                Obj::FiniteSeqSet(_) | Obj::SeqSet(_) | Obj::MatrixSet(_) | Obj::StructObj(_)
            ) {
                return Ok(false);
            }
            for binding in &group.params {
                let object: Obj =
                    Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
                let membership: Fact =
                    InFact::new(object, carrier.clone(), result.statement.line_file.clone()).into();
                parameters.push((binding, carrier, membership));
            }
        }

        let expected_store_count = parameters.len() + result.statement.facts.len();
        if result.common.infers.store_fact_outputs.len() != expected_store_count {
            return Err(format!(
                "trust-have retained {} store outputs for {expected_store_count} parameter/fact effects",
                result.common.infers.store_fact_outputs.len()
            ));
        }
        for (index, ((_, _, expected), store)) in parameters
            .iter()
            .zip(result.common.infers.store_fact_outputs.iter())
            .enumerate()
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "trust-have parameter store {index} changed `{expected}` to `{}`",
                    store.itself_and_why_itself_is_stored.0
                ));
            }
            if store.fact_id.is_none() {
                return Err(format!("trust-have parameter store {index} has no FactId"));
            }
        }
        for (index, (expected, store)) in result
            .statement
            .facts
            .iter()
            .zip(
                result
                    .common
                    .infers
                    .store_fact_outputs
                    .iter()
                    .skip(parameters.len()),
            )
            .enumerate()
        {
            if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "trust-have attached fact store {index} changed `{expected}` to `{}`",
                    store.itself_and_why_itself_is_stored.0
                ));
            }
            if store.fact_id.is_none() {
                return Err(format!(
                    "trust-have attached fact store {index} has no FactId"
                ));
            }
        }

        for (index, (binding, carrier, membership)) in parameters.iter().enumerate() {
            let store = &result.common.infers.store_fact_outputs[index];
            let fact_id = store.fact_id.expect("validated trust-have FactId");
            let name = lean_identifier(binding.name());
            let rendered_carrier = render_obj(carrier, &self.environment_stack)?;
            let function = match carrier {
                Obj::FnSet(function_set) => {
                    Some(LeanTargetFunctionTypeRepresentation::lower(function_set)?)
                }
                _ => None,
            };
            let declared_type = if let Some(function) = &function {
                render_function_type(function, &self.environment_stack)?
            } else {
                format!("{rendered_carrier}.Carrier")
            };
            let rendered_value = if function.is_some() {
                format!("(@{name})")
            } else {
                name.clone()
            };
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), rendered_value.clone())
                .is_some()
            {
                return Err(format!(
                    "trust-have reused compiler SymbolId for `{}`",
                    binding.name()
                ));
            }
            self.declarations
                .push(format!("axiom {name} : {declared_type}"));

            let proposition = render_fact(membership, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact Litex.In.own {rendered_carrier} {rendered_value}"
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name.clone());
            self.environment_stack
                .fact_propositions
                .insert(fact_id, membership.clone());
            if let Some(function) = function {
                self.environment_stack.function_bindings.insert(
                    fact_id,
                    FunctionBinding {
                        symbol_id: binding.id(),
                        function,
                        membership_proof_name: theorem_name,
                        direct: true,
                    },
                );
            }
            self.next_fact_name_index += 1;
        }

        for (fact, store) in result.statement.facts.iter().zip(
            result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .skip(parameters.len()),
        ) {
            let fact_id = store.fact_id.expect("validated trust-have FactId");
            let proposition = match fact {
                Fact::ForallFact(forall) => {
                    render_forall_fact_type(forall, &self.environment_stack)?
                }
                _ => render_fact(fact, &self.environment_stack)?,
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations
                .push(format!("axiom {theorem_name} : {proposition}"));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Leaf`: preserve an explicit Litex source axiom as an explicit Lean
    /// axiom and register the exact stored forall FactId. This is a source
    /// trust boundary, not a compiler-invented escape hatch.
    pub(in super::super) fn compile_source_axiom_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessAxiomStmtResult,
    ) -> Result<(), String> {
        let axiom_fact: Fact = result.statement.forall_fact.clone().into();
        let well_definedness = result
            .well_definedness
            .as_ref()
            .ok_or_else(|| "source axiom retained no well-definedness Result".to_string())?;
        let SuccessVerifyFactWellDefinedProofResult::ForallFact(recursive) =
            well_definedness.proof.as_ref()
        else {
            return Err("source axiom retained no recursive forall well-definedness".into());
        };
        if recursive.statement.to_string() != result.statement.forall_fact.to_string() {
            return Err("source axiom well-definedness changed its forall proposition".into());
        }
        if !result.common.infers.rule_applications.is_empty() {
            return Err("source axiom retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("source axiom must retain exactly one store effect".into());
        };
        if store.itself_and_why_itself_is_stored.0.to_string() != axiom_fact.to_string()
            || !store.inferred_facts.is_empty()
            || !store.inferred_fact_ids.is_empty()
        {
            return Err(
                "source axiom changed its stored proposition or inferred consequences".into(),
            );
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| "source axiom store has no FactId".to_string())?;
        let proposition =
            render_forall_fact_type(&result.statement.forall_fact, &self.environment_stack)?;
        let axiom_name = lean_identifier(&result.statement.name);
        self.declarations
            .push(format!("axiom {axiom_name} : {proposition}"));
        self.environment_stack
            .fact_names
            .insert(fact_id, axiom_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, axiom_fact);
        Ok(())
    }
}
