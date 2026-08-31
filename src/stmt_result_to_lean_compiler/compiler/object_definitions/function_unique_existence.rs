//! Functions selected from a verified pointwise unique-existence theorem.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Compile the first target family for `have fn ... by exist!`: one total
    /// unary function whose explicit proof process contains the witness
    /// construction.  The source Result remains authoritative for the local
    /// assumptions, witness proof, uniqueness proof, and both published
    /// facts.  Domain-constrained and telescope functions fail closed until
    /// their dependent application ABI is implemented.
    pub(in super::super) fn compile_have_fn_by_forall_exist_unique_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveFnByForallExistUniqueStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.source_forall_check.is_some()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Ok(false);
        }

        let mut runtime = Runtime::default();
        runtime.ensure_execution_frame_for_parse();
        let function_body = runtime
            .direct_fn_set_body_for_have_fn_by_forall_exist_unique(&result.statement)
            .map_err(|error| error.trace_message())?;
        let function_set = FnSet::from_body(function_body).map_err(|error| error.to_string())?;
        let function = LeanTargetFunctionTypeRepresentation::lower(&function_set)?;
        if function_uses_telescope(&function) || !function.domain_facts.is_empty() {
            return Ok(false);
        }
        validate_unary_function_type(&function)?;

        let source_existential = match result.statement.forall.then_facts.as_slice() {
            [ExistOrAndChainAtomicFact::ExistFact(existential)]
                if existential.is_exist_unique() =>
            {
                existential
            }
            _ => {
                return Err(
                    "have-fn unique-existence Result changed its sole `exist!` conclusion".into(),
                )
            }
        };

        let parameters = result
            .statement
            .forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameters.len() != 1 || !matches!(parameters[0].1, ParamType::Obj(_)) {
            return Ok(false);
        }
        let source_parameter_set = parameter_set(&parameters[0].1)?;
        if matches!(
            source_parameter_set,
            Obj::StandardSet(StandardSet::Z | StandardSet::RPos)
        ) {
            return Ok(false);
        }
        let source_parameter_facts = result
            .statement
            .forall
            .typed_parameters
            .groups
            .iter()
            .flat_map(|group| {
                let parameter_set = match &group.param_type {
                    ParamType::Obj(set) => Some(set),
                    _ => None,
                };
                group.params.iter().filter_map(move |parameter| {
                    parameter_set.map(|set| {
                        Fact::from(InFact::new(
                            obj_for_bound_param_in_scope(parameter),
                            set.clone(),
                            result.statement.line_file.clone(),
                        ))
                    })
                })
            })
            .collect::<Vec<_>>();
        if source_parameter_facts.len() != 1
            || !result.statement.forall.dom_facts.is_empty()
            || !verification.proof_scope.assumption_components.is_empty()
        {
            return Ok(false);
        }
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            &verification.proof_scope.assumption_infers,
            &source_parameter_facts,
            "have-fn unique-existence local parameter",
        )?;
        let parameter_fact_id = assumption_fact_ids[0];

        let function_object: Obj = Identifier::new_bound(
            result.statement.fn_name().to_string(),
            result.statement.symbol_binding.as_ref(),
        )
        .into();
        let expected_membership: Fact = InFact::new(
            function_object,
            function_set.clone().into(),
            result.statement.line_file.clone(),
        )
        .into();
        let reconstructed_property: Fact = runtime
            .direct_property_forall_for_have_fn_by_forall_exist_unique(&result.statement)
            .map_err(|error| error.trace_message())?
            .into();
        if !result.common.infers.rule_applications.is_empty() {
            return Ok(false);
        }
        let [membership_store, property_store] = result.common.infers.store_fact_outputs.as_slice()
        else {
            return Err(
                "have-fn unique-existence Result must publish membership and property".into(),
            );
        };
        if !frozen_result_facts_align(
            &membership_store.itself_and_why_itself_is_stored.0,
            &expected_membership,
        ) || !membership_store.inferred_facts.is_empty()
            || !membership_store.inferred_fact_ids.is_empty()
            || !property_store.inferred_facts.is_empty()
            || !property_store.inferred_fact_ids.is_empty()
        {
            return Err(
                "have-fn unique-existence outer effects changed their direct store shape".into(),
            );
        }
        let expected_property = property_store.itself_and_why_itself_is_stored.0.clone();
        let (Fact::ForallFact(reconstructed_forall), Fact::ForallFact(stored_forall)) =
            (&reconstructed_property, &expected_property)
        else {
            return Err("have-fn unique-existence property is not a forall fact".into());
        };
        if runtime
            .alpha_normalized_forall_cache_key(reconstructed_forall)
            .map_err(|error| error.trace_message())?
            != runtime
                .alpha_normalized_forall_cache_key(stored_forall)
                .map_err(|error| error.trace_message())?
        {
            return Err(
                "have-fn unique-existence stored property changed its source contract".into(),
            );
        }
        let stored_fact_ids = [
            membership_store.fact_id.ok_or_else(|| {
                "have-fn unique-existence membership store has no FactId".to_string()
            })?,
            property_store.fact_id.ok_or_else(|| {
                "have-fn unique-existence property store has no FactId".to_string()
            })?,
        ];

        let theorem_well_definedness = self
            .collect_well_definedness_to_lean_compilation_context(&verification.well_definedness)?;
        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(theorem_well_definedness.clone());
        let local_compilation: Result<Option<(String, String)>, String> = (|| {
            let (source_binding, source_parameter_type) = &parameters[0];
            let source_parameter_set = parameter_set(source_parameter_type)?;
            let parameter_fact = &source_parameter_facts[0];
            validate_object_parameter_premise(
                source_binding.id(),
                source_parameter_set,
                parameter_fact,
            )?;
            self.environment_stack
                .symbol_names
                .insert(source_binding.id(), "__arg".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, parameter_fact.clone());
            install_parameter_fact_aliases(
                source_binding.id(),
                parameter_fact_id,
                parameter_fact,
                "__arg_in",
                source_parameter_set,
                &mut self.environment_stack,
            )?;

            let recursive_well_definedness = verification
                .well_definedness
                .recursive
                .as_deref()
                .ok_or_else(|| {
                    "have-fn unique-existence Result has no recursive well-definedness root"
                        .to_string()
                })?;
            let compiled_well_definedness = self.compile_precollected_well_definedness_context(
                theorem_well_definedness,
                &[recursive_well_definedness],
            )?;
            self.environment_stack.well_definedness = Some(compiled_well_definedness);

            let mut local_lines = Vec::new();
            let mut existence_body = None;
            for (proof_index, proof_result) in verification.proof_steps.iter().enumerate() {
                if let StmtResult::Success(SuccessStmtResult::Witness(
                    SuccessWitnessStmtResult::WitnessExistFact(witness),
                )) = proof_result
                {
                    if existence_body.is_some() {
                        return Err(
                            "have-fn unique-existence proof retained more than one witness step"
                                .into(),
                        );
                    }
                    let Some(witness_verification) = &witness.verification else {
                        return Ok(None);
                    };
                    let body = self
                        .construct_lean_existence_proof_from_unique_witness_result(
                            source_existential,
                            &witness.statement.equal_tos,
                            witness.statement.proof.len(),
                            &witness.statement.line_file,
                            witness_verification,
                        )?
                        .ok_or_else(|| {
                            "have-fn unique-existence witness has no Lean proof consumer"
                                .to_string()
                        })?;
                    existence_body = Some(body);
                    continue;
                }
                let Some(lines) =
                    self.compile_stmt_result_as_local_proof_steps(proof_result, proof_index + 1)?
                else {
                    return Ok(None);
                };
                local_lines.extend(lines);
            }
            let body = existence_body.ok_or_else(|| {
                "have-fn unique-existence proof retained no witness construction".to_string()
            })?;
            local_lines.push(format!("exact {}", body.proof_expression));
            Ok(Some((body.proposition, local_lines.join("\n"))))
        })();
        self.environment_stack.pop_local_environment();
        let Some((existence_proposition, existence_proof)) = local_compilation? else {
            return Ok(false);
        };

        let name = lean_identifier(result.statement.fn_name());
        let existence_name = format!("{name}__exists");
        let domain = render_lean_source_for_target_set_representation(
            &function.parameters[0].set,
            &self.environment_stack,
        )?;
        self.declarations.push(format!(
            "private theorem {existence_name} :\n  ∀ {{__alpha : Type}} (__arg : __alpha) (__arg_in : Litex.In __arg {domain}),\n    {existence_proposition} := by\n  intro __alpha __arg __arg_in\n{}",
            indent_lines(&existence_proof, 2)
        ));

        let function_type = render_function_type(&function, &self.environment_stack)?;
        let function_set_source = render_function_set(&function, &self.environment_stack)?;
        self.declarations.push(format!(
            "noncomputable def {name} : {function_type} :=\n  {{ call := fun {{__alpha}} __arg __arg_in =>\n      Classical.choose ({existence_name} __arg __arg_in) }}"
        ));
        self.environment_stack
            .symbol_names
            .insert(result.statement.symbol_binding.id(), name.clone());

        let membership_name = format!("__fact{}", self.next_fact_name_index);
        let membership_proposition = render_fact(&expected_membership, &self.environment_stack)?;
        self.declarations.push(format!(
            "theorem {membership_name} : {membership_proposition} := by\n  exact Litex.In.own {function_set_source} {name}"
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[0], membership_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[0], expected_membership);
        self.environment_stack.function_bindings.insert(
            stored_fact_ids[0],
            FunctionBinding {
                symbol_id: result.statement.symbol_binding.id(),
                function: function.clone(),
                membership_proof_name: membership_name,
                direct: true,
            },
        );
        self.next_fact_name_index += 1;

        let property_name = format!("__fact{}", self.next_fact_name_index);
        let property_well_definedness = result
            .published_property_well_definedness
            .as_ref()
            .ok_or_else(|| {
                "have-fn unique-existence Result lost its published-property WD evidence"
                    .to_string()
            })?;
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(property_wd_forall)) =
            property_well_definedness.recursive.as_deref()
        else {
            return Err("have-fn unique-existence property WD has no recursive forall root".into());
        };
        if runtime
            .alpha_normalized_forall_cache_key(&property_wd_forall.statement)
            .map_err(|error| error.trace_message())?
            != runtime
                .alpha_normalized_forall_cache_key(stored_forall)
                .map_err(|error| error.trace_message())?
        {
            return Err("have-fn unique-existence property WD changed its published forall".into());
        }

        // The runtime-derived property application is synthesized after the
        // source proof has finished, so it has no parser occurrence id.  Build
        // its Lean type from the same source existential body and the exact
        // compiler-owned function application instead of pretending that a
        // parser-owned application certificate exists.
        self.environment_stack.push_inherited_environment();
        let property_body: Result<String, String> = (|| {
            let source_binding = &parameters[0].0;
            self.environment_stack
                .symbol_names
                .insert(source_binding.id(), "__arg".into());
            self.environment_stack
                .fact_names
                .insert(parameter_fact_id, "__arg_in".into());
            self.environment_stack
                .fact_propositions
                .insert(parameter_fact_id, source_parameter_facts[0].clone());
            install_parameter_fact_aliases(
                source_binding.id(),
                parameter_fact_id,
                &source_parameter_facts[0],
                "__arg_in",
                source_parameter_set,
                &mut self.environment_stack,
            )?;

            let witness_groups = &source_existential.typed_parameters().groups;
            let [witness_group] = witness_groups.as_slice() else {
                return Err("have-fn unique-existence property requires one witness group".into());
            };
            let [witness_binding] = witness_group.params.as_slice() else {
                return Err("have-fn unique-existence property requires one witness binder".into());
            };
            let witness_set = parameter_set(&witness_group.param_type)?;
            let rendered_domain = render_obj(source_parameter_set, &self.environment_stack)?;
            let rendered_codomain = render_obj(witness_set, &self.environment_stack)?;
            let selected_value = format!(
                "(Litex.fnApplyOwn (domain := {rendered_domain}) (codomain := {rendered_codomain}) {name} {} __arg __arg_in)",
                self.environment_stack
                    .fact_names
                    .get(&stored_fact_ids[0])
                    .ok_or_else(|| {
                        "have-fn unique-existence membership theorem is unavailable".to_string()
                    })?
            );
            self.environment_stack
                .symbol_names
                .insert(witness_binding.id(), selected_value.clone());
            install_exact_predicate_carrier_value(
                witness_binding.id(),
                witness_set,
                &selected_value,
                &mut self.environment_stack,
            )?;
            render_fact(
                &source_existential.facts()[0].from_ref_to_cloned_fact(),
                &self.environment_stack,
            )
        })();
        self.environment_stack.pop_local_environment();
        let property_body = property_body?;
        let property_proposition = format!(
            "∀ {{__alpha : Type}} (__arg : __alpha) (__arg_in : Litex.In __arg {domain}), {property_body}"
        );
        self.declarations.push(format!(
            "theorem {property_name} : {property_proposition} := by\n  intro __alpha __arg __arg_in\n  simpa [{name}, Litex.fnApplyOwn] using\n    (Classical.choose_spec ({existence_name} __arg __arg_in)).choose_spec"
        ));
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[1], property_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[1], expected_property);
        self.next_fact_name_index += 1;
        Ok(true)
    }
}
