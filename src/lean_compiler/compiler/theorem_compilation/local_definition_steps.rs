//! Local object and by-definition proof steps.

use super::super::*;

impl StmtResultToLeanCompiler {
    /// Compile a typed `have x T = value` inside a structured theorem proof.
    /// Both the symbol and every fact publication retain their verifier-owned
    /// identities in the surrounding local compiler frame.
    pub(in super::super) fn compile_have_obj_equal_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessHaveObjEqualStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let verification = result.verification.as_ref().ok_or_else(|| {
            "local have-object equality has no structured value type-check results".to_string()
        })?;
        let bindings_with_types = result
            .statement
            .param_def
            .collect_param_bindings_with_types();
        if bindings_with_types.len() != result.statement.objs_equal_to.len()
            || bindings_with_types.len() != verification.type_checks.len()
        {
            return Err(
                "local have-object equality changed its binding, value, or type-check count".into(),
            );
        }
        if bindings_with_types.len() != 1 {
            return Ok(None);
        }

        let ((binding, param_type), value) = bindings_with_types
            .first()
            .zip(result.statement.objs_equal_to.first())
            .expect("one binding and value were checked above");
        let defined_object: Obj =
            Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into();
        let stored_type_fact = object_type_fact_for_compiler_definition(
            defined_object.clone(),
            param_type,
            result.statement.line_file.clone(),
        );
        let stored_equality: Fact = EqualFact::new(
            defined_object.clone(),
            value.clone(),
            result.statement.line_file.clone(),
        )
        .into();
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &[stored_type_fact.clone(), stored_equality.clone()],
            "local have-object equality",
        )?;

        let expected_value_type = object_type_fact_for_compiler_definition(
            value.clone(),
            param_type,
            result.statement.line_file.clone(),
        );
        let type_check = verification.type_checks[0]
            .factual_success()
            .ok_or_else(|| "local have-object value has no factual type-check child".to_string())?;
        if type_check.fact().to_string() != expected_value_type.to_string() {
            return Err(format!(
                "local have-object value type-check changed `{expected_value_type}` to `{}`",
                type_check.fact()
            ));
        }
        let type_check_proof = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(type_check)?
            .ok_or_else(|| {
                format!(
                    "StmtResult-to-Lean compiler has no direct proof consumer for `{expected_value_type}`"
                )
            })?;

        let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
        let rendered_value = if matches!(param_type, ParamType::Set(_)) {
            render_set_definition_value(&lowered_value, &self.environment_stack)?
        } else {
            render_lean_source_for_native_target_object_representation(
                &lowered_value,
                &self.environment_stack,
            )?
        };
        let lean_name = lean_identifier(binding.name());
        if self
            .environment_stack
            .symbol_names
            .insert(binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate local compiler symbol identity for `{}`",
                binding.name()
            ));
        }

        let rendered_type_fact = render_fact(&stored_type_fact, &self.environment_stack)?;
        let rendered_equality = render_fact(&stored_equality, &self.environment_stack)?;
        let type_name = format!("__step{proof_step_index}_type");
        let equality_name = format!("__step{proof_step_index}_equality");
        let let_binding = if matches!(
            param_type,
            ParamType::Set(_) | ParamType::Obj(Obj::PowerSet(_))
        ) {
            format!("let {lean_name} : Litex.Set := {rendered_value}")
        } else {
            format!("let {lean_name} := {rendered_value}")
        };
        let mut lines = vec![
            let_binding,
            format!(
                "have {type_name} : {rendered_type_fact} := by\n  unfold {lean_name}\n  exact {type_check_proof}"
            ),
            format!(
                "have {equality_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ),
        ];
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[0], type_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[0], stored_type_fact.clone());
        self.environment_stack
            .fact_names
            .insert(stored_fact_ids[1], equality_name);
        self.environment_stack
            .fact_propositions
            .insert(stored_fact_ids[1], stored_equality.clone());
        self.environment_stack
            .transparent_object_definitions
            .insert(
                binding.id(),
                CompilerTransparentObjectDefinition {
                    value: value.clone(),
                    defining_equality: stored_equality,
                    defining_equality_fact_id: stored_fact_ids[1],
                },
            );

        if result.common.infers.rule_applications.is_empty()
            && result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .all(|output| {
                    output.inferred_facts.is_empty() && output.inferred_fact_ids.is_empty()
                })
        {
            if !type_check.store.infers.is_empty() {
                return Err(
                    "local have-object type check unexpectedly published inference effects".into(),
                );
            }
            return Ok(Some(lines));
        }
        self.compile_local_power_set_definition_inferences(
            param_type,
            value,
            &defined_object,
            type_check,
            proof_step_index,
            &mut lines,
            &result.common.infers,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "local have-object equality",
        )?;
        Ok(Some(lines))
    }

    fn compile_local_power_set_definition_inferences(
        &mut self,
        param_type: &ParamType,
        value: &Obj,
        defined_object: &Obj,
        type_check: &SuccessFactStmtResult,
        proof_step_index: usize,
        lines: &mut Vec<String>,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let ParamType::Obj(Obj::PowerSet(power_set)) = param_type else {
            return Err("local have-object retained unsupported inferred consequences".into());
        };
        let Obj::SetBuilder(builder) = value else {
            return Err("local power-set definition inference requires a set-builder value".into());
        };
        let (SuccessFactProofResult::BuiltinRule(builtin)
        | SuccessFactProofResult::BuiltinStrategy(builtin)) = type_check.proof()
        else {
            return Err("local power-set definition lost its typed builtin type-check".into());
        };
        if !matches!(
            builtin.evidence.typed(),
            Some(BuiltinRuleEvidence::SetBuilderInPowerSetViaParamSubset)
        ) {
            return Err(
                "local power-set definition type-check changed its typed rule identity".into(),
            );
        }
        let [type_check_store] = type_check.store.infers.store_fact_outputs.as_slice() else {
            return Err(
                "local power-set definition type-check changed its single transient store".into(),
            );
        };
        if type_check_store.fact_id.is_some()
            || type_check_store
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != type_check.fact().to_string()
            || !type_check_store.inferred_facts.is_empty()
            || !type_check_store.inferred_fact_ids.is_empty()
            || !type_check.store.infers.rule_applications.is_empty()
        {
            return Err(
                "local power-set definition type-check changed its transient effects".into(),
            );
        }
        let [child] = builtin.subgoals.as_slice() else {
            return Err(
                "local power-set definition type-check must retain one subset child".into(),
            );
        };
        let child = child
            .factual_success()
            .ok_or_else(|| "local power-set definition subset child is not factual".to_string())?;
        if !child.store.infers.is_empty() {
            return Err("local power-set definition subset child published effects".into());
        }
        let child_fact = child.fact();
        let (child_left, child_right) = subset_parts(&child_fact)?;
        if !objs_equal_with_nested_binder_alpha_equivalence(builder.param_set.as_ref(), child_left)
            || !objs_equal_with_nested_binder_alpha_equivalence(power_set.set.as_ref(), child_right)
        {
            return Err("local power-set definition subset child changed its endpoints".into());
        }
        let child_proof = self
            .construct_lean_proof_from_direct_fact_result(child)?
            .ok_or_else(|| {
                "local power-set definition subset child has no typed Lean consumer".to_string()
            })?;

        let [type_store, equality_store] = infers.store_fact_outputs.as_slice() else {
            return Err("local power-set definition changed its two direct stores".into());
        };
        if !equality_store.inferred_facts.is_empty()
            || !equality_store.inferred_fact_ids.is_empty()
            || type_store.inferred_facts.len() != 2
            || type_store.inferred_fact_ids.len() != 2
        {
            return Err("local power-set definition changed its inferred effect arity".into());
        }
        let expected_subset: Fact = SubsetFact::new(
            defined_object.clone(),
            (*power_set.set).clone(),
            type_check.fact().line_file().clone(),
        )
        .into();
        if type_store.inferred_facts[0].to_string() != expected_subset.to_string() {
            return Err("local power-set definition changed its inferred subset".into());
        }
        let subset_fact_id = type_store.inferred_fact_ids[0]
            .ok_or_else(|| "local power-set definition subset has no FactId".to_string())?;

        let [application] = infers.rule_applications.as_slice() else {
            return Err(
                "local power-set definition must retain one elementwise-membership rule".into(),
            );
        };
        if !matches!(
            application.rule,
            InferRule::SubsetImpliesElementwiseMembershipForall(_)
        ) || application.premises.len() != 1
            || application.conclusions.len() != 1
            || application.premises[0].fact_id != Some(subset_fact_id)
            || application.premises[0].fact.to_string() != expected_subset.to_string()
        {
            return Err(
                "local power-set definition changed its typed elementwise-membership rule".into(),
            );
        }
        let elementwise = &application.conclusions[0];
        let elementwise_fact_id = type_store.inferred_fact_ids[1]
            .ok_or_else(|| "local power-set elementwise fact has no FactId".to_string())?;
        if elementwise.fact_id != Some(elementwise_fact_id)
            || elementwise.fact.to_string() != type_store.inferred_facts[1].to_string()
        {
            return Err(
                "local power-set definition changed its elementwise conclusion identity".into(),
            );
        }
        validate_set_inclusion_elementwise_forall_inference_target(
            &application.rule,
            &expected_subset,
            &elementwise.fact,
        )?;

        let subset_name = format!("__step{proof_step_index}_subset");
        let subset_proposition = render_fact(&expected_subset, &self.environment_stack)?;
        lines.push(format!(
            "have {subset_name} : {subset_proposition} := by\n  unfold {}\n  exact Litex.Rules.setBuilderSubsetViaParamSubset ({child_proof})",
            render_obj(defined_object, &self.environment_stack)?
        ));
        self.environment_stack
            .fact_names
            .insert(subset_fact_id, subset_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(subset_fact_id, expected_subset);

        let elementwise_name = format!("__step{proof_step_index}_elements");
        let elementwise_proposition = render_fact(&elementwise.fact, &self.environment_stack)?;
        lines.push(format!(
            "have {elementwise_name} : {elementwise_proposition} := by\n  exact {subset_name}"
        ));
        self.environment_stack
            .fact_names
            .insert(elementwise_fact_id, elementwise_name);
        self.environment_stack
            .fact_propositions
            .insert(elementwise_fact_id, elementwise.fact.clone());
        Ok(())
    }

    /// `Combine`: a local `let` publishes its symbol and exact defining
    /// equality only in the compiler frame that owns the surrounding proof.
    /// The recursive proof-step consumer therefore needs no separate
    /// local-environment IR and no Runtime lookup.
    pub(in super::super) fn compile_let_obj_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessLetObjStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        if !result.common.infers.rule_applications.is_empty() {
            return Err("local let-object retained unexpected typed inference rules".into());
        }
        let [store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("local let-object must retain exactly one defining store".into());
        };
        if !store.inferred_facts.is_empty() || !store.inferred_fact_ids.is_empty() {
            return Err("local let-object defining store retained inferred facts".into());
        }

        let statement = &result.statement;
        let source_name = statement.symbol_binding.name();
        let lean_name = lean_identifier(source_name);
        let rendered_value = render_obj(&statement.value, &self.environment_stack)?;
        let defined_object: Obj =
            Identifier::new_bound(source_name.to_string(), statement.symbol_binding.as_ref())
                .into();
        let defining_equality: Fact = EqualFact::new(
            defined_object,
            statement.value.clone(),
            statement.line_file.clone(),
        )
        .into();
        if store.itself_and_why_itself_is_stored.0.to_string() != defining_equality.to_string() {
            return Err("local let-object Result changed its defining equality".into());
        }
        let defining_equality_fact_id = store
            .fact_id
            .ok_or_else(|| "local let-object defining equality has no FactId".to_string())?;

        if self
            .environment_stack
            .symbol_names
            .insert(statement.symbol_binding.id(), lean_name.clone())
            .is_some()
        {
            return Err(format!(
                "duplicate local compiler symbol identity for `{source_name}`"
            ));
        }
        let rendered_equality = render_fact(&defining_equality, &self.environment_stack)?;
        let theorem_name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(defining_equality_fact_id, theorem_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(defining_equality_fact_id, defining_equality.clone());
        self.environment_stack
            .transparent_object_definitions
            .insert(
                statement.symbol_binding.id(),
                CompilerTransparentObjectDefinition {
                    value: statement.value.clone(),
                    defining_equality,
                    defining_equality_fact_id,
                },
            );

        Ok(Some(vec![
            format!("let {lean_name} := {rendered_value}"),
            format!(
                "have {theorem_name} : {rendered_equality} := by\n  unfold {lean_name}\n  exact Litex.Same.refl {rendered_value}"
            ),
        ]))
    }

    /// `Combine`: retain a `by def` statement as one local proof step. The
    /// target FactId becomes visible in the current compiler frame, while an
    /// inferred definition component must either cite an already visible
    /// exact FactId or carry its own recursive component proof.
    pub(in super::super) fn compile_by_definition_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessByDefStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let mut prerequisite_lines = Vec::new();
        if let Some(verification) = &result.verification {
            for (clause_index, check) in verification.clause_checks.iter().enumerate() {
                let check = check.factual_success().ok_or_else(|| {
                    format!("by-definition clause check {clause_index} is not factual")
                })?;
                if matches!(check.proof(), SuccessFactProofResult::ForallProof(_)) {
                    let Some(lines) =
                        self.compile_direct_forall_fact_result_as_local_proof_steps(check)?
                    else {
                        return Err(format!(
                            "by-definition forall clause {clause_index} has no local binder compiler"
                        ));
                    };
                    prerequisite_lines.extend(lines);
                }
            }
        }
        let Some(proof) = self.construct_lean_proof_from_by_definition_stmt_result(result)? else {
            return Ok(None);
        };
        if result
            .common
            .infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Ok(None);
        }
        let [output] = result.common.infers.store_fact_outputs.as_slice() else {
            return Ok(None);
        };
        if output.itself_and_why_itself_is_stored.0.to_string() != proof.target.fact.to_string()
            || output.inferred_facts.len() != output.inferred_fact_ids.len()
        {
            return Err("local by-definition Result changed its target or inferred effects".into());
        }
        let target_fact_id = output
            .fact_id
            .ok_or_else(|| "local by-definition target has no FactId".to_string())?;
        let target_name = format!("__step{proof_step_index}");
        prerequisite_lines.push(format!(
            "have {target_name} : {} := by\n  exact {}",
            proof.target.proposition, proof.target.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(target_fact_id, target_name);
        self.environment_stack
            .fact_propositions
            .insert(target_fact_id, proof.target.fact.clone());
        self.install_compiled_by_definition_component_bindings(&proof.components)?;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "local by-definition Result",
        )?;
        Ok(Some(prerequisite_lines))
    }
}
