//! Object equality declarations.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_have_obj_equal_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjEqualStmtResult,
    ) -> Result<(), String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "have-object equality has no structured value type-check results".to_string()
        })?;
        let bindings_with_types = result
            .statement
            .param_def
            .collect_param_bindings_with_types();
        if bindings_with_types.len() != result.statement.objs_equal_to.len()
            || bindings_with_types.len() != verification.type_checks.len()
        {
            return Err(
                "have-object equality changed its binding, value, or type-check count".into(),
            );
        }
        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
        {
            return Err("have-object equality retained unsupported inferred consequences".into());
        }

        let mut expected_stored_facts = Vec::with_capacity(bindings_with_types.len() * 2);
        for ((binding, param_type), value) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
        {
            let defined_object: Obj =
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
            expected_stored_facts.push(object_type_fact_for_compiler_definition(
                defined_object.clone(),
                param_type,
                result.statement.line_file.clone(),
            ));
            expected_stored_facts.push(
                EqualFact::new(
                    defined_object,
                    value.clone(),
                    result.statement.line_file.clone(),
                )
                .into(),
            );
        }
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &expected_stored_facts,
            "have-object equality",
        )?;

        for (index, ((binding, param_type), value)) in bindings_with_types
            .iter()
            .zip(result.statement.objs_equal_to.iter())
            .enumerate()
        {
            let expected_value_type = object_type_fact_for_compiler_definition(
                value.clone(),
                param_type,
                result.statement.line_file.clone(),
            );
            let type_check = verification.type_checks[index]
                .factual_success()
                .ok_or_else(|| {
                    format!(
                        "have-object value `{}` has no successful type-check child Result",
                        binding.name()
                    )
                })?;
            if type_check.fact().to_string() != expected_value_type.to_string() {
                return Err(format!(
                    "have-object value type-check changed `{expected_value_type}` to `{}`",
                    type_check.fact()
                ));
            }

            let lean_name = lean_identifier(binding.name());
            if matches!(param_type, ParamType::Set(_)) {
                let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
                let rendered_value =
                    render_set_definition_value(&lowered_value, &self.environment_stack)?;
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), lean_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "duplicate compiler symbol identity for `{}`",
                        binding.name()
                    ));
                }
                self.declarations.push(format!(
                    "abbrev {lean_name} : Litex.Set := {rendered_value}"
                ));

                // A set alias is a real Result layer, not only a target-side
                // abbreviation. Publish both frozen store identities so a
                // recursive child may cite the set classification or the
                // defining equality from the current compiler environment.
                let stored_type_fact = expected_stored_facts[index * 2].clone();
                let stored_equality = expected_stored_facts[index * 2 + 1].clone();
                let stored_type_fact_id = stored_fact_ids[index * 2];
                let stored_equality_fact_id = stored_fact_ids[index * 2 + 1];
                let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
                let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;

                let type_theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {type_theorem_name} : {rendered_type_fact} := by\n  exact True.intro"
                ));
                self.environment_stack
                    .fact_names
                    .insert(stored_type_fact_id, type_theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(stored_type_fact_id, stored_type_fact);
                self.next_fact_name_index += 1;

                let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
                self.declarations.push(format!(
                    "theorem {equality_theorem_name} : {rendered_equality} := by\n  exact Litex.Same.refl {rendered_value}"
                ));
                self.environment_stack
                    .fact_names
                    .insert(stored_equality_fact_id, equality_theorem_name);
                self.environment_stack
                    .fact_propositions
                    .insert(stored_equality_fact_id, stored_equality.clone());
                self.environment_stack
                    .transparent_object_definitions
                    .insert(
                        binding.id(),
                        CompilerTransparentObjectDefinition {
                            value: value.clone(),
                            defining_equality: stored_equality,
                            defining_equality_fact_id: stored_equality_fact_id,
                        },
                    );
                self.next_fact_name_index += 1;
                continue;
            }

            let ParamType::Obj(_) = param_type else {
                return Err(format!(
                    "have-object `{}` has an unsupported non-membership type",
                    binding.name()
                ));
            };
            if bindings_with_types.len() != 1 {
                return Err(
                    "native have-object definitions currently require exactly one object".into(),
                );
            }
            let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
            let rendered_value = render_lean_source_for_native_target_object_representation(
                &lowered_value,
                &self.environment_stack,
            )?;
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), lean_name.clone())
                .is_some()
            {
                return Err(format!(
                    "duplicate compiler symbol identity for `{}`",
                    binding.name()
                ));
            }
            self.declarations
                .push(format!("noncomputable def {lean_name} := {rendered_value}"));

            let type_check_proof = self.construct_lean_proof_from_fact_result_without_storing(
                &verification.type_checks[index],
                &expected_value_type,
                "have-object type check",
            )?;
            let stored_type_fact = expected_stored_facts[index * 2].clone();
            let stored_equality = expected_stored_facts[index * 2 + 1].clone();
            let stored_type_fact_id = stored_fact_ids[index * 2];
            let stored_equality_fact_id = stored_fact_ids[index * 2 + 1];
            let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
            let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;

            let type_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {type_theorem_name} : {rendered_type_fact} := by\n  unfold {lean_name}\n  exact {type_check_proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_type_fact_id, type_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_type_fact_id, stored_type_fact);
            self.next_fact_name_index += 1;

            let equality_theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {equality_theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ));
            self.environment_stack
                .fact_names
                .insert(stored_equality_fact_id, equality_theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(stored_equality_fact_id, stored_equality.clone());
            self.environment_stack
                .transparent_object_definitions
                .insert(
                    binding.id(),
                    CompilerTransparentObjectDefinition {
                        value: value.clone(),
                        defining_equality: stored_equality,
                        defining_equality_fact_id: stored_equality_fact_id,
                    },
                );
            self.environment_stack
                .runtime_resolved_numeric_substitutions
                .insert(binding.substitution_key(), value.clone());
            self.environment_stack
                .runtime_resolved_numeric_definition_names
                .push(lean_name);
            self.next_fact_name_index += 1;
        }
        Ok(())
    }
}
