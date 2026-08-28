use super::*;

impl StmtResultToLeanCompiler {
    /// `Combine`: compile the witness's local proof-step Results, its checked
    /// parameter requirement, and its checked body fact before publishing the
    /// introduced existential under the exact outer store FactId.
    pub(super) fn compile_witness_exist_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessWitnessExistFactResult,
    ) -> Result<bool, String> {
        let Some(proof_body) =
            self.construct_lean_proof_from_witness_exist_fact_stmt_result(result)?
        else {
            return Ok(false);
        };
        let existential: Fact = result.statement.exist_fact_in_witness.clone().into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &existential,
            "existential witness outer effect",
        )?;

        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof_body.proposition, proof_body.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, existential);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: compile the ordered local proof-step Results, consume the
    /// retained witness-membership check, and publish the target set's
    /// nonemptiness under the exact outer store FactId. The local compiler
    /// environment is inherited for the proof body and discarded afterward.
    pub(super) fn compile_witness_nonempty_set_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessWitnessNonemptySetResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.proof_steps.len() != result.statement.proof.len() {
            return Err("nonempty-set witness changed its source proof-step order".into());
        }

        let target_fact: Fact = IsNonemptySetFact::new(
            result.statement.set.clone(),
            result.statement.line_file.clone(),
        )
        .into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &target_fact,
            "nonempty-set witness outer effect",
        )?;

        self.environment_stack.push_inherited_environment();
        let compilation: Result<Option<CompiledNonemptySetWitnessProofBody>, String> = (|| {
            let mut proof_lines = Vec::new();
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Err(format!(
                        "nonempty-set witness proof step {} has no local compiler consumer: {:?}",
                        proof_step_index + 1,
                        proof_step,
                    ));
                };
                proof_lines.extend(lines);
            }

            let membership_check =
                verification
                    .nonempty_check
                    .factual_success()
                    .ok_or_else(|| {
                        "nonempty-set witness retained a non-factual final check".to_string()
                    })?;
            let expected_membership: Fact = InFact::new(
                result.statement.obj.clone(),
                result.statement.set.clone(),
                result.statement.line_file.clone(),
            )
            .into();
            if membership_check.fact().to_string() != expected_membership.to_string()
                || membership_check.store.fact.to_string() != expected_membership.to_string()
                || !membership_check.store.infers.is_empty()
            {
                // Function-set witnesses use a different retained check: the
                // return set's nonemptiness. That route remains an explicit
                // later compiler family rather than being guessed here.
                if matches!(result.statement.set, Obj::FnSet(_)) {
                    return Ok(None);
                }
                return Err(
                    "nonempty-set witness changed its final membership check or published effects"
                        .into(),
                );
            }
            let Some(membership_proof) =
                self.construct_lean_proof_from_direct_fact_result(membership_check)?
            else {
                return Ok(None);
            };
            let membership_proposition =
                render_fact(&expected_membership, &self.environment_stack)?;
            let proposition = render_fact(&target_fact, &self.environment_stack)?;
            proof_lines.push(format!(
                "have __nonempty_membership : {membership_proposition} := by\n  exact {membership_proof}"
            ));
            proof_lines.push(
                "rcases __nonempty_membership with ⟨__nonempty_witness, __nonempty_same⟩".into(),
            );
            proof_lines.push("exact ⟨__nonempty_witness⟩".into());
            Ok(Some(CompiledNonemptySetWitnessProofBody {
                proposition,
                local_proof_lines: proof_lines,
            }))
        })();
        self.environment_stack.pop_local_environment();
        let Some(compiled_body) = compilation? else {
            return Ok(false);
        };

        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            compiled_body.proposition,
            indent_lines(&compiled_body.local_proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, target_fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// Reuse the complete nonempty-witness compiler inside a named theorem.
    /// Its one generated declaration is compiler-owned syntax, so replacing
    /// the leading `theorem` with `have` keeps the exact FactId publication
    /// while retaining every enclosing local binder.
    pub(super) fn compile_witness_nonempty_set_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessWitnessNonemptySetResult,
    ) -> Result<Option<Vec<String>>, String> {
        let declaration_count = self.declarations.len();
        let fact_index = self.next_fact_name_index;
        if !self.compile_witness_nonempty_set_stmt_result_to_lean_source(result)? {
            return Ok(None);
        }
        if self.declarations.len() != declaration_count + 1
            || self.next_fact_name_index != fact_index + 1
        {
            return Err(
                "local nonempty-set witness generated an unexpected declaration count".into(),
            );
        }
        let declaration = self
            .declarations
            .pop()
            .expect("validated one generated nonempty-set witness declaration");
        let body = declaration.strip_prefix("theorem ").ok_or_else(|| {
            "local nonempty-set witness generated an unexpected declaration shape".to_string()
        })?;
        Ok(Some(vec![format!("have {body}")]))
    }

    pub(super) fn construct_lean_proof_from_witness_exist_fact_stmt_result(
        &mut self,
        result: &SuccessWitnessExistFactResult,
    ) -> Result<Option<CompiledExistentialWitnessProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        self.construct_lean_proof_from_plain_existential_witness_result(
            &result.statement.exist_fact_in_witness,
            &result.statement.equal_tos,
            result.statement.proof.len(),
            &result.statement.line_file,
            verification,
        )
    }

    /// Shared `Combine` body for the explicit and predicate-backed witness
    /// statements. The parent Result chooses the wrapper; this helper consumes
    /// the same recursively retained ordinary existential verification.
    pub(super) fn construct_lean_proof_from_plain_existential_witness_result(
        &mut self,
        existential: &ExistFactEnum,
        witness_objects: &[Obj],
        source_proof_step_count: usize,
        line_file: &LineFile,
        verification: &SuccessVerifyWitnessExistResult,
    ) -> Result<Option<CompiledExistentialWitnessProofBody>, String> {
        if !existential.is_plain_exist()
            || existential.typed_parameters().number_of_params() != 1
            || existential.facts().len() != 1
            || witness_objects.len() != 1
        {
            return Err(
                "StmtResultToLeanCompiler currently requires one positive witness and one body fact"
                    .into(),
            );
        }
        let group = &existential.typed_parameters().groups[0];
        if group.params.len() != 1 || !matches!(group.param_type, ParamType::Obj(_)) {
            return Err(
                "StmtResultToLeanCompiler currently requires one membership witness".into(),
            );
        }
        if verification.proof_steps.len() != source_proof_step_count
            || verification.parameter_checks.len() != 1
            || verification.body_checks.len() != 1
            || verification.uniqueness_check.is_some()
        {
            return Err(
                "existential witness Result changed its parameter, proof-step, body, or uniqueness mapping"
                    .into(),
            );
        }

        let source_set = parameter_set(&group.param_type)?;
        let witness_object = &witness_objects[0];
        self.install_existential_witness_anonymous_function_occurrence_aliases(existential)?;
        let rendered_witness = render_obj(witness_object, &self.environment_stack)?;
        let proposition = render_existential_fact(existential, &self.environment_stack)?;

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            if self
                .environment_stack
                .symbol_names
                .insert(group.params[0].id(), rendered_witness.clone())
                .is_some()
            {
                return Err("existential witness reused a visible binder SymbolId".into());
            }
            self.environment_stack
                .existential_names
                .insert(group.params[0].name().to_string(), rendered_witness.clone());

            let mut proof_lines = Vec::with_capacity(verification.proof_steps.len() + 1);
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Err(format!(
                        "existential witness proof step {} has no local compiler consumer: {:?}",
                        proof_step_index + 1,
                        proof_step,
                    ));
                };
                proof_lines.extend(lines);
            }

            let Some(parameter_check) = verification.parameter_checks[0].as_deref() else {
                return Err(
                    "existential membership witness has no parameter-check child Result".into(),
                );
            };
            let parameter_check = parameter_check.factual_success().ok_or_else(|| {
                "existential witness parameter check is not a successful fact Result".to_string()
            })?;
            let expected_parameter_fact: Fact = InFact::new(
                witness_object.clone(),
                source_set.clone(),
                line_file.clone(),
            )
            .into();
            if parameter_check.fact().to_string() != expected_parameter_fact.to_string()
                || !parameter_check.store.infers.is_empty()
            {
                return Err(
                    "existential witness parameter check changed its instantiated requirement"
                        .into(),
                );
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(parameter_check)?
            else {
                return Err(format!(
                    "existential witness parameter check has no direct proof consumer: {:?}",
                    parameter_check.proof()
                ));
            };

            let body_check = verification.body_checks[0]
                .factual_success()
                .ok_or_else(|| {
                    "existential witness body check is not a successful fact Result".to_string()
                })?;
            if !body_check.store.infers.is_empty() {
                return Err(
                    "existential witness body check unexpectedly published inference effects"
                        .into(),
                );
            }
            let substitutions = existential
                .typed_parameters()
                .param_defs_and_args_to_param_to_arg_map(witness_objects);
            let mut substitution_runtime = Runtime::default();
            substitution_runtime.ensure_execution_frame_for_parse();
            let expected_body = substitution_runtime
                .inst_fact(
                    &existential.facts()[0].from_ref_to_cloned_fact(),
                    &substitutions,
                    SubstitutionMode::ResultProjection,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "existential witness body substitution replay failed: {}",
                        error.trace_message()
                    )
                })?;
            let expected_key = substitution_runtime
                .equivalent_proposition_lookup_key_for_fact(&expected_body)
                .map_err(|error| error.trace_message())?;
            let retained_key = substitution_runtime
                .equivalent_proposition_lookup_key_for_fact(&body_check.fact())
                .map_err(|error| error.trace_message())?;
            if expected_key != retained_key {
                return Err(format!(
                    "existential witness body check changed `{expected_body}` to `{}`",
                    body_check.fact()
                ));
            }
            let Some(body_proof) = self.construct_lean_proof_from_direct_fact_result(body_check)?
            else {
                return Err(format!(
                    "existential witness body check has no direct proof consumer: {:?}",
                    body_check.proof()
                ));
            };

            let function_or_dynamic_carrier = matches!(source_set, Obj::FnSet(_))
                || set_requires_heterogeneous_carrier(source_set);
            let witness_has_complex_host =
                match LeanTargetObjectRepresentation::lower(witness_object)? {
                    LeanTargetObjectRepresentation::Symbol { symbol_id, .. } => self
                        .environment_stack
                        .complex_host_values
                        .contains(&symbol_id),
                    _ => false,
                };
            let (carrier_witness, parameter_proof, body_proof) = if function_or_dynamic_carrier {
                (
                    format!("_, {rendered_witness}"),
                    parameter_proof,
                    body_proof,
                )
            } else if witness_has_complex_host {
                (rendered_witness, parameter_proof, body_proof)
            } else {
                let lowered_set = LeanTargetObjectRepresentation::lower(source_set)?;
                let parameter_proof_term = format!("({parameter_proof})");
                let selected_witness = membership_numeric_value(
                        &lowered_set,
                        &rendered_witness,
                        &parameter_proof_term,
                    )
                    .ok_or_else(|| {
                        format!(
                            "existential witness `{witness_object}` has no canonical numeric representation in `{source_set}`"
                        )
                    })?;
                let selected_membership = membership_numeric_proof(
                        &lowered_set,
                        &rendered_witness,
                        &parameter_proof_term,
                    )
                    .ok_or_else(|| {
                        format!(
                            "existential witness `{witness_object}` has no canonical complex membership proof in `{source_set}`"
                        )
                    })?;
                let source_to_selected = membership_numeric_equality(
                        &lowered_set,
                        &rendered_witness,
                        &parameter_proof_term,
                    )
                    .ok_or_else(|| {
                        format!(
                            "existential witness `{witness_object}` has no semantic bridge to its canonical numeric representation"
                        )
                    })?;
                let Fact::AtomicFact(AtomicFact::EqualFact(body_equality)) =
                    &existential.facts()[0].from_ref_to_cloned_fact()
                else {
                    return Err(
                            "numeric existential witness transport currently requires one equality body"
                                .into(),
                        );
                };
                let source_context = self.environment_stack.clone();
                let mut selected_context = source_context.clone();
                selected_context
                    .symbol_names
                    .insert(group.params[0].id(), selected_witness.clone());
                selected_context
                    .numeric_representations
                    .insert(group.params[0].id(), selected_witness.clone());
                let selected_body_proof = render_equality_across_representative(
                    body_equality,
                    &source_context,
                    &selected_context,
                    &rendered_witness,
                    &selected_witness,
                    &source_to_selected,
                    &body_proof,
                )?;
                (selected_witness, selected_membership, selected_body_proof)
            };
            proof_lines.push(format!(
                "exact ⟨{carrier_witness}, ({parameter_proof}), ({body_proof})⟩"
            ));
            Ok(Some(CompiledExistentialWitnessProofBody {
                proposition,
                proof_expression: format!("(by\n{})", indent_lines(&proof_lines.join("\n"), 2)),
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    /// A witness target can repeat an anonymous function from its enclosing
    /// theorem goal under a fresh parser occurrence. Reuse is permitted only
    /// when the complete alpha-normalized function object selects exactly one
    /// Result-owned WD certificate; rendering then uses that certificate's
    /// original binder identities.
    fn install_existential_witness_anonymous_function_occurrence_aliases(
        &mut self,
        existential: &ExistFactEnum,
    ) -> Result<(), String> {
        fn collect_from_object(
            object: &Obj,
            functions: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            if let Obj::AnonymousFn(function) = object {
                if let Some(occurrence_id) = function.source_occurrence_id {
                    functions.push((occurrence_id, obj_equality_key(object)));
                }
            }
            if let Obj::FnObj(application) = object {
                let head: Obj = application.head.as_ref().clone().into();
                collect_from_object(&head, functions);
            }
            let _: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
                object,
                object,
                &mut |child, _| {
                    collect_from_object(child, functions);
                    Ok(true)
                },
            );
        }

        let mut functions = Vec::new();
        for argument in existential.get_args_from_fact_ref() {
            collect_from_object(argument, &mut functions);
        }
        functions.sort_by_key(|(occurrence_id, _)| occurrence_id.value());
        functions.dedup_by_key(|(occurrence_id, _)| occurrence_id.value());
        if functions.is_empty() {
            return Ok(());
        }

        let context = self
            .environment_stack
            .well_definedness
            .as_mut()
            .ok_or_else(|| {
                "existential witness anonymous function has no active theorem WD Result".to_string()
            })?;
        for (source_occurrence, semantic_key) in functions {
            if context.anonymous_functions.contains_key(&source_occurrence) {
                continue;
            }
            let owners = context
                .anonymous_functions
                .iter()
                .filter_map(|(owner_occurrence, certificate)| {
                    (obj_equality_key(&certificate.source_function) == semantic_key)
                        .then_some(*owner_occurrence)
                })
                .collect::<Vec<_>>();
            let [owner_occurrence] = owners.as_slice() else {
                return Err(format!(
                    "existential witness anonymous function occurrence {} has {} alpha-equivalent theorem-WD owners",
                    source_occurrence.value(),
                    owners.len()
                ));
            };
            if let Some(previous) = context
                .anonymous_function_occurrence_aliases
                .insert(source_occurrence, *owner_occurrence)
            {
                if previous != *owner_occurrence {
                    return Err(format!(
                        "existential witness anonymous function occurrence {} changed its WD owner",
                        source_occurrence.value()
                    ));
                }
            }
        }
        Ok(())
    }

    /// `Combine`: prove the instantiated existential from its ordinary child
    /// Result, fold it through the already compiled concrete predicate, and
    /// publish the primary predicate, argument-membership, and existential
    /// facts under the exact IDs retained by the statement's store output.
    pub(super) fn compile_witness_atomic_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessWitnessAtomicFactResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.definition.name != result.statement.atomic_fact.predicate.to_string()
            || verification.definition.iff_facts.len() != 1
        {
            return Err("atomic witness changed its concrete predicate definition".into());
        }
        let predicate_name = verification.definition.name.clone();
        let predicate_binding = self
            .environment_stack
            .predicate_bindings
            .get(&predicate_name)
            .ok_or_else(|| {
                format!("atomic witness cites unavailable predicate `{predicate_name}`")
            })?;
        if predicate_binding
            .definition
            .as_ref()
            .is_none_or(|definition| definition.to_string() != verification.definition.to_string())
        {
            return Err("atomic witness changed the compiled predicate definition".into());
        }
        let predicate_lean_name = predicate_binding.lean_name.clone();
        let predicate_exact_parameters = predicate_binding.exact_parameters.clone();

        let existential_proof = self.construct_lean_proof_from_plain_existential_witness_result(
            &verification.instantiated_existential,
            &result.statement.witnesses,
            result.statement.proof.len(),
            &result.statement.line_file,
            &verification.witness_verification,
        )?;
        let Some(existential_proof) = existential_proof else {
            return Ok(false);
        };

        let parameter_verification = verification.definition_parameter_verification.as_ref();
        if !parameter_verification.infers.is_empty() {
            return Err(
                "atomic witness parameter verification unexpectedly published effects".into(),
            );
        }
        let mut expected_parameter_facts = Vec::new();
        let mut definition_arguments = Vec::new();
        let mut argument_index = 0;
        for group in &verification.definition.typed_parameters.groups {
            let set = match &group.param_type {
                ParamType::Obj(set) => set,
                _ => return Ok(false),
            };
            for parameter in &group.params {
                let argument = result
                    .statement
                    .atomic_fact
                    .body
                    .get(argument_index)
                    .ok_or_else(|| "atomic witness lost a predicate argument".to_string())?;
                expected_parameter_facts.push(Fact::from(InFact::new(
                    argument.clone(),
                    set.clone(),
                    result.statement.line_file.clone(),
                )));
                let exact = predicate_exact_parameters
                    .get(argument_index)
                    .copied()
                    .ok_or_else(|| {
                        "atomic witness predicate lost its exact-parameter classification"
                            .to_string()
                    })?;
                definition_arguments.push((parameter.id(), set.clone(), argument.clone(), exact));
                argument_index += 1;
            }
        }
        if argument_index != result.statement.atomic_fact.body.len()
            || parameter_verification.checks.len() != expected_parameter_facts.len()
        {
            return Err("atomic witness changed its predicate argument/type mapping".into());
        }

        let mut parameter_proofs = Vec::with_capacity(expected_parameter_facts.len());
        for (index, (check_result, expected_fact)) in parameter_verification
            .checks
            .iter()
            .zip(expected_parameter_facts.iter())
            .enumerate()
        {
            let check = check_result
                .factual_success()
                .ok_or_else(|| format!("atomic witness parameter check {index} is not factual"))?;
            if check.fact().to_string() != expected_fact.to_string()
                || check.store.fact.to_string() != expected_fact.to_string()
                || !check.store.infers.is_empty()
            {
                return Err(format!(
                    "atomic witness parameter check {index} changed its expected fact"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Ok(false);
            };
            parameter_proofs.push((check, expected_fact.clone(), proof));
        }

        let target_fact: Fact =
            AtomicFact::NormalAtomicFact(result.statement.atomic_fact.clone()).into();
        let [store_output] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("atomic witness must retain exactly one outer store output".into());
        };
        if result
            .common
            .infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
            || result.common.infers.rule_applications.len() != parameter_proofs.len() + 1
            || store_output.itself_and_why_itself_is_stored.0.to_string() != target_fact.to_string()
            || store_output.inferred_facts.len() != parameter_proofs.len() + 1
            || store_output.inferred_fact_ids.len() != store_output.inferred_facts.len()
        {
            return Err("atomic witness changed its ordered outer effects".into());
        }
        let target_fact_id = store_output
            .fact_id
            .ok_or_else(|| "atomic witness primary store has no FactId".to_string())?;
        for (index, (_, expected_fact, _)) in parameter_proofs.iter().enumerate() {
            if store_output.inferred_facts[index].to_string() != expected_fact.to_string() {
                return Err(format!(
                    "atomic witness inferred parameter fact {index} changed its proposition"
                ));
            }
            let inferred_fact_id = store_output.inferred_fact_ids[index]
                .ok_or_else(|| format!("atomic witness parameter effect {index} has no FactId"))?;
            if parameter_proofs[index].0.store.fact_id != Some(inferred_fact_id) {
                return Err(format!(
                    "atomic witness parameter check {index} and outer effect disagree on FactId"
                ));
            }
        }
        let existential_fact: Fact = verification.instantiated_existential.clone().into();
        if store_output
            .inferred_facts
            .last()
            .is_none_or(|fact| fact.to_string() != existential_fact.to_string())
        {
            return Err("atomic witness changed its inferred existential fact".into());
        }
        store_output
            .inferred_fact_ids
            .last()
            .copied()
            .flatten()
            .ok_or_else(|| "atomic witness inferred existential has no FactId".to_string())?;

        let target_proposition = render_fact(&target_fact, &self.environment_stack)?;
        let mut clause_context = self.environment_stack.clone();
        for (symbol_id, _, argument, _) in &definition_arguments {
            clause_context
                .symbol_names
                .insert(*symbol_id, render_obj(argument, &self.environment_stack)?);
        }
        let mut transported_existential = format!(
            "(show {} from {})",
            existential_proof.proposition, existential_proof.proof_expression
        );
        let mut definition_components = Vec::with_capacity(parameter_proofs.len() + 1);
        for (index, (symbol_id, set, argument, exact)) in definition_arguments.iter().enumerate() {
            if !exact {
                definition_components.push(parameter_proofs[index].2.clone());
                continue;
            }
            let source_value = render_obj(argument, &self.environment_stack)?;
            let target_value =
                render_exact_predicate_argument(argument, set, &self.environment_stack)?;
            definition_components.push(format!(
                "Litex.In.own {} {target_value}",
                render_obj(set, &self.environment_stack)?
            ));
            if source_value == target_value {
                continue;
            }
            let exact_to_source = render_exact_predicate_argument_same_to_source(
                argument,
                set,
                &self.environment_stack,
            )?;
            let mut next = clause_context.clone();
            next.symbol_names.insert(*symbol_id, target_value.clone());
            install_exact_predicate_carrier_value(*symbol_id, set, &target_value, &mut next)?;
            let Fact::ExistFact(definition_existential) = &verification.definition.iff_facts[0]
            else {
                return Err(
                    "atomic witness exact-parameter transport requires an existential definition clause"
                        .into(),
                );
            };
            transported_existential = render_existential_equality_across_representative(
                definition_existential,
                &clause_context,
                &next,
                &source_value,
                &target_value,
                &format!("Litex.Same.symm ({exact_to_source})"),
                &transported_existential,
            )?;
            clause_context = next;
        }
        definition_components.push(transported_existential);
        let target_proof = right_associated_conjunction_proof(&definition_components)?;
        let target_theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {target_theorem_name} : {target_proposition} := by\n  unfold {predicate_lean_name}\n  exact {target_proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(target_fact_id, target_theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(target_fact_id, target_fact);
        self.next_fact_name_index += 1;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "atomic witness Result",
        )?;
        Ok(true)
    }

    /// `Combine`: resolve the exact existential source proof, introduce the
    /// selected object name, and publish each retained projection under the
    /// exact store FactId owned by this elimination Result.
    pub(super) fn compile_obtain_obj_from_exist_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromExistFactResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if result.statement.fact.to_string() != verification.source_exist_fact.to_string() {
            return Err("existential elimination changed its source existential".into());
        }
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            None,
        )
    }

    pub(super) fn compile_obtain_obj_from_exist_fact_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessObtainObjFromExistFactResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if result.statement.fact.to_string() != verification.source_exist_fact.to_string() {
            return Err("local existential elimination changed its source existential".into());
        }
        let existential = &verification.source_exist_fact;
        if !existential.is_plain_exist()
            || existential.typed_parameters().number_of_params() != 1
            || existential.facts().len() != 1
            || result.statement.equal_tos.len() != 1
            || verification.witness_type_facts.len() != 1
            || verification.instantiated_body_facts.len() != 1
            || verification.includes_uniqueness
        {
            return Ok(None);
        }
        validate_typed_infer_result_identity_completeness(
            &result.common.infers,
            "local existential elimination",
        )?;
        if result
            .common
            .infers
            .rule_applications
            .iter()
            .any(|application| {
                !defined_predicate_infer_rule(&application.rule)
                    && !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
        {
            return Ok(None);
        }

        let expected_stored_facts = [
            verification.witness_type_facts[0].clone(),
            verification.instantiated_body_facts[0].clone(),
        ];
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &result.common.infers,
            &expected_stored_facts,
            "local existential elimination projections",
        )?;
        let [witness_type_fact_id, body_fact_id] = stored_fact_ids.as_slice() else {
            unreachable!("two expected projection facts produced two FactIds")
        };

        let source_result = verification
            .source_result
            .factual_success()
            .ok_or_else(|| "local existential elimination source is not factual".to_string())?;
        if !source_result.store.infers.is_empty() {
            return Err("local existential elimination source Result gained effects".into());
        }
        let Some(source_proof) = self
            .construct_lean_proof_from_direct_fact_result(source_result)
            .map_err(|error| format!("local existential source proof: {error}"))?
        else {
            return Ok(None);
        };
        let source_fact: Fact = existential.clone().into();
        if !one_witness_existentials_are_alpha_equal(
            &source_result.fact(),
            &source_fact,
            &self.environment_stack,
        )? {
            return Err("local existential elimination source changed its cited fact".into());
        }
        let source_proposition = render_fact(&source_fact, &self.environment_stack)
            .map_err(|error| format!("local existential source proposition: {error}"))?;

        let group = &existential.typed_parameters().groups[0];
        if group.params.len() != 1 || !matches!(group.param_type, ParamType::Obj(_)) {
            return Ok(None);
        }
        let source_set = parameter_set(&group.param_type)?;
        if set_requires_heterogeneous_carrier(source_set) || matches!(source_set, Obj::FnSet(_)) {
            return Ok(None);
        }
        let binding = &result.statement.equal_tos[0];
        let witness_name = lean_identifier(binding.name());
        if self
            .environment_stack
            .symbol_names
            .insert(binding.id(), witness_name.clone())
            .is_some()
        {
            return Err(format!(
                "local existential elimination reused SymbolId for `{}`",
                binding.name()
            ));
        }
        self.environment_stack
            .complex_host_values
            .insert(binding.id());

        let witness_type_fact = &verification.witness_type_facts[0];
        let body_fact = &verification.instantiated_body_facts[0];
        let rendered_type_fact = render_fact(witness_type_fact, &self.environment_stack)?;
        let expected_type_fact = format!(
            "Litex.In {witness_name} {}",
            render_obj(source_set, &self.environment_stack)?
        );
        if rendered_type_fact != expected_type_fact {
            return Err("local existential elimination changed its witness type projection".into());
        }
        let type_name = format!("__step{proof_step_index}_type");
        let body_name = format!("__step{proof_step_index}_body");
        self.environment_stack
            .fact_names
            .insert(*witness_type_fact_id, type_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(*witness_type_fact_id, witness_type_fact.clone());
        install_parameter_fact_aliases(
            binding.id(),
            *witness_type_fact_id,
            witness_type_fact,
            &type_name,
            source_set,
            &mut self.environment_stack,
        )?;
        let mut source_template_environment = self.environment_stack.clone();
        source_template_environment
            .symbol_names
            .insert(group.params[0].id(), witness_name.clone());
        source_template_environment
            .existential_names
            .insert(group.params[0].name().to_string(), witness_name.clone());
        let lowered_source_set = LeanTargetObjectRepresentation::lower(source_set)?;
        let exact_template_witness = if matches!(
            lowered_source_set,
            LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex)
        ) {
            witness_name.clone()
        } else {
            format!("(Litex.In.rep {witness_name} {type_name})")
        };
        source_template_environment
            .exact_carrier_values
            .insert(group.params[0].id(), exact_template_witness);
        install_numeric_representations_from_membership(
            group.params[0].id(),
            &lowered_source_set,
            &witness_name,
            &type_name,
            &mut source_template_environment,
        );
        let expected_body = render_fact(
            &existential.facts()[0].from_ref_to_cloned_fact(),
            &source_template_environment,
        )?;
        let retained_body = render_fact(body_fact, &self.environment_stack)?;
        if expected_body != retained_body {
            return Err(format!(
                "local existential elimination changed its body projection: expected `{expected_body}`, retained `{retained_body}`"
            ));
        }
        self.environment_stack
            .fact_names
            .insert(*body_fact_id, body_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(*body_fact_id, body_fact.clone());
        let mut proof_lines = vec![format!(
            "rcases (show {source_proposition} from {source_proof}) with ⟨{witness_name}, {type_name}, {body_name}⟩"
        )];
        let direct_source_keys = result
            .common
            .infers
            .rule_applications
            .iter()
            .filter(|application| {
                infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
            .filter_map(|application| {
                application.premises.first().and_then(|premise| {
                    premise
                        .fact_id
                        .map(|fact_id| (fact_id, premise.fact.to_string()))
                })
            })
            .collect::<HashSet<_>>();
        let direct_infers = SuccessInferResult {
            store_fact_outputs: result
                .common
                .infers
                .store_fact_outputs
                .iter()
                .filter(|output| {
                    output.fact_id.is_some_and(|fact_id| {
                        direct_source_keys.contains(&(
                            fact_id,
                            output.itself_and_why_itself_is_stored.0.to_string(),
                        ))
                    })
                })
                .cloned()
                .collect(),
            rule_applications: result
                .common
                .infers
                .rule_applications
                .iter()
                .filter(|application| {
                    infer_rule_has_direct_compiler_environment_consumer(&application.rule)
                })
                .cloned()
                .collect(),
        };
        let allowed_sources = expected_stored_facts
            .iter()
            .cloned()
            .zip(stored_fact_ids.iter().copied())
            .map(|(fact, fact_id)| (fact_id, fact))
            .collect::<Vec<_>>();
        self.compile_typed_inference_results_as_local_have_statements(
            &direct_infers,
            &allowed_sources,
            &mut proof_lines,
            "local existential elimination direct inference",
        )?;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "local existential elimination",
        )?;
        Ok(Some(proof_lines))
    }

    /// `Combine`: the statement itself is the existential source. The adapter
    /// verifies that execution retained that exact binder and body before the
    /// shared elimination compiler consumes its recursively named children.
    pub(super) fn compile_have_obj_by_exist_facts_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessHaveObjByExistFactsStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let existential = &verification.source_exist_fact;
        if result.statement.param_def.to_string() != existential.typed_parameters().to_string()
            || result
                .statement
                .facts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != existential
                    .facts()
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("object-by-existential Result changed its binder or body facts".into());
        }
        let bindings = result.statement.param_def.collect_param_bindings();
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &bindings,
            &result.common,
            verification,
            None,
        )
    }

    /// `Combine`: the concrete predicate projection is retained as the source
    /// fact Result. The shared compiler obtains the witness only after that
    /// exact recursive `DefinitionProjection` proof has been constructed.
    pub(super) fn compile_obtain_obj_from_atomic_fact_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromAtomicFactResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let source_result = verification
            .source_result
            .factual_success()
            .ok_or_else(|| {
                "predicate-backed existential elimination source is not factual".to_string()
            })?;
        let SuccessFactProofResult::BuiltinRule(source_builtin) = source_result.proof() else {
            return Ok(false);
        };
        let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
            source_builtin.evidence.typed()
        else {
            return Ok(false);
        };
        if evidence.fact.to_string() != result.statement.fact.to_string() {
            return Err("predicate-backed existential elimination changed its source fact".into());
        }
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            None,
        )
    }

    /// `Combine`: the nested theorem application constructs one local
    /// existential conclusion proof. This parent consumes that proof as its
    /// source and publishes only the selected witness projections.
    pub(super) fn compile_obtain_obj_from_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessObtainObjFromThmResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let source_result = verification
            .source_result
            .non_factual_success()
            .ok_or_else(|| {
                "theorem-backed existential elimination source is not a statement Result"
                    .to_string()
            })?;
        let SuccessStmtResult::ReleaseThmStmt(theorem_application) = source_result else {
            return Err(
                "theorem-backed existential elimination retained another source statement".into(),
            );
        };
        if theorem_application.statement.name.to_string() != result.statement.thm_name.to_string()
            || theorem_application
                .statement
                .args
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                != result
                    .statement
                    .args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err(
                "theorem-backed existential elimination changed its theorem application".into(),
            );
        }
        let Some(mut conclusions) = self
            .construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
                theorem_application,
            )?
        else {
            return Ok(false);
        };
        if conclusions.len() != 1 {
            return Err(
                "theorem-backed existential elimination requires one direct conclusion".into(),
            );
        }
        let source = conclusions
            .pop()
            .expect("one theorem conclusion was checked above");
        self.compile_positive_single_witness_existential_elimination_result_to_lean_source(
            &result.statement.equal_tos,
            &result.common,
            verification,
            Some(CompiledFactProofBody {
                fact: source.fact,
                proposition: source.proposition,
                proof_expression: source.proof_expression,
            }),
        )
    }

    /// Shared `Combine` for the currently reviewed existential-elimination
    /// shape. Statement-family adapters above own syntax-specific validation;
    /// this method owns the one source proof, witness binding, and two stored
    /// projection effects.
    pub(super) fn compile_positive_single_witness_existential_elimination_result_to_lean_source(
        &mut self,
        introduced_bindings: &[SymbolBinding],
        common: &SuccessStmtCommonResult,
        verification: &SuccessVerifyExistentialEliminationResult,
        prepared_source_proof: Option<CompiledFactProofBody>,
    ) -> Result<bool, String> {
        let existential = &verification.source_exist_fact;
        if !existential.is_plain_exist()
            || existential.typed_parameters().number_of_params() != 1
            || existential.facts().len() != 1
            || introduced_bindings.len() != 1
            || verification.witness_type_facts.len() != 1
            || verification.instantiated_body_facts.len() != 1
            || verification.includes_uniqueness
        {
            return Ok(false);
        }
        if !common.infers.rule_applications.is_empty()
            || common.infers.store_fact_outputs.iter().any(|output| {
                !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
            })
        {
            return Ok(false);
        }
        let expected_stored_facts = vec![
            verification.witness_type_facts[0].clone(),
            verification.instantiated_body_facts[0].clone(),
        ];
        let stored_fact_ids = exact_ordered_fact_ids_from_store_results(
            &common.infers,
            &expected_stored_facts,
            "existential elimination projections",
        )?;

        let source_fact: Fact = existential.clone().into();
        let source_proof_body = if let Some(source_proof) = prepared_source_proof {
            source_proof
        } else {
            let source_result = verification
                .source_result
                .factual_success()
                .ok_or_else(|| {
                    "existential elimination source is not a successful fact Result".to_string()
                })?;
            if !source_result.store.infers.is_empty() {
                return Err("existential elimination source Result gained effects".into());
            }
            let Some(source_proof) =
                self.construct_lean_proof_from_direct_fact_result(source_result)?
            else {
                return Ok(false);
            };
            let fact = source_result.fact();
            CompiledFactProofBody {
                proposition: render_fact(&fact, &self.environment_stack)?,
                fact,
                proof_expression: source_proof,
            }
        };
        if !one_witness_existentials_are_alpha_equal(
            &source_proof_body.fact,
            &source_fact,
            &self.environment_stack,
        )? {
            return Err("existential elimination source Result changed its cited fact".into());
        }
        let source_proposition = render_fact(&source_fact, &self.environment_stack)?;
        if source_proof_body.proposition != source_proposition {
            return Err("existential elimination source proof changed its Lean proposition".into());
        }
        let typed_source_proof = format!(
            "(show {source_proposition} from {})",
            source_proof_body.proof_expression
        );

        let group = &existential.typed_parameters().groups[0];
        if group.params.len() != 1 || !matches!(group.param_type, ParamType::Obj(_)) {
            return Ok(false);
        }
        let source_set = parameter_set(&group.param_type)?;
        let binding = &introduced_bindings[0];
        let witness_name = lean_identifier(binding.name());
        let mut result_environment_stack = self.environment_stack.clone();
        if result_environment_stack
            .symbol_names
            .insert(binding.id(), witness_name.clone())
            .is_some()
        {
            return Err(format!(
                "existential elimination reused SymbolId for `{}`",
                binding.name()
            ));
        }
        let mut source_template_environment_stack = result_environment_stack.clone();
        source_template_environment_stack
            .symbol_names
            .insert(group.params[0].id(), witness_name.clone());
        source_template_environment_stack
            .existential_names
            .insert(group.params[0].name().to_string(), witness_name.clone());

        let expected_requirement = format!(
            "Litex.In {witness_name} {}",
            render_obj(source_set, &result_environment_stack)?
        );
        let retained_requirement = render_fact(
            &verification.witness_type_facts[0],
            &result_environment_stack,
        )?;
        let expected_body = render_fact(
            &existential.facts()[0].from_ref_to_cloned_fact(),
            &source_template_environment_stack,
        )?;
        let retained_body = render_fact(
            &verification.instantiated_body_facts[0],
            &result_environment_stack,
        )?;
        if retained_requirement != expected_requirement || retained_body != expected_body {
            return Err("existential elimination changed a retained projection role".into());
        }

        // Only the selected object is visible after this Result. The source
        // existential binder above exists solely while validating the two
        // recursively retained projection children.
        self.environment_stack = result_environment_stack;

        let dynamic_carrier = set_requires_heterogeneous_carrier(source_set);
        let function_carrier = matches!(source_set, Obj::FnSet(_));
        if !dynamic_carrier && !function_carrier {
            self.environment_stack
                .complex_host_values
                .insert(binding.id());
        }
        let carrier_name = format!("__carrier_{witness_name}");
        let specification = if dynamic_carrier || function_carrier {
            self.declarations.push(format!(
                "noncomputable def {carrier_name} : {} := Classical.choose ({typed_source_proof})",
                if function_carrier { "Type 1" } else { "Type" }
            ));
            self.declarations.push(format!(
                "noncomputable def {witness_name} : {carrier_name} :=\n  Classical.choose (Classical.choose_spec ({typed_source_proof}))"
            ));
            format!("Classical.choose_spec (Classical.choose_spec ({typed_source_proof}))")
        } else {
            self.declarations.push(format!(
                "noncomputable def {witness_name} : ℂ := Classical.choose ({typed_source_proof})"
            ));
            format!("Classical.choose_spec ({typed_source_proof})")
        };

        let unfold = if dynamic_carrier || function_carrier {
            format!("{witness_name} {carrier_name}")
        } else {
            witness_name.clone()
        };
        for ((fact, fact_id), selector) in expected_stored_facts
            .iter()
            .zip(stored_fact_ids.iter())
            .zip([".1", ".2"])
        {
            let proposition = render_fact(fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  unfold {unfold}\n  exact ({specification}){selector}"
            ));
            self.environment_stack
                .fact_names
                .insert(*fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(*fact_id, fact.clone());
            self.next_fact_name_index += 1;
        }
        if let Fact::AtomicFact(AtomicFact::NormalAtomicFact(certificate)) =
            &verification.instantiated_body_facts[0]
        {
            if certificate.predicate.to_string() == IS_REAL_LEAST_UPPER_BOUND {
                if certificate.body.len() != 2
                    || obj_equality_key(&certificate.body[1])
                        != obj_equality_key(&obj_for_bound_param_in_scope(binding))
                {
                    return Err(
                        "real LUB existential projection changed its certified witness".into(),
                    );
                }
                let membership_proof = self
                    .environment_stack
                    .fact_names
                    .get(&stored_fact_ids[0])
                    .cloned()
                    .ok_or_else(|| {
                        "real LUB witness membership has no compiled FactId".to_string()
                    })?;
                self.environment_stack
                    .numeric_representations
                    .insert(binding.id(), witness_name.clone());
                self.environment_stack
                    .numeric_real_values
                    .insert(binding.id(), format!("Litex.OrderValue {witness_name}"));
                self.environment_stack
                    .numeric_representation_equalities
                    .insert(binding.id(), format!("Litex.Same.refl {witness_name}"));
                self.environment_stack
                    .numeric_representation_memberships
                    .insert(binding.id(), membership_proof);
            }
        }
        Ok(true)
    }

    pub(super) fn compile_by_cases_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByCasesStmtResult,
    ) -> Result<bool, String> {
        let Some(proofs) = self.construct_lean_proofs_from_by_cases_stmt_result(result)? else {
            return Ok(false);
        };
        let fact_ids = validate_compiled_fact_proof_effects(
            &result.common.infers,
            &proofs,
            &self.environment_stack,
            "by-cases exported goals",
        )?;
        for (proof, fact_id) in proofs.into_iter().zip(fact_ids) {
            let Some(fact_id) = fact_id else {
                continue;
            };
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {} := by\n  exact {}",
                proof.proposition, proof.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, proof.fact);
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    pub(super) fn compile_by_extension_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByExtensionStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_extension_stmt_result(result)? else {
            return Ok(false);
        };
        let [fact_id] = validate_compiled_fact_proof_effects(
            &result.common.infers,
            std::slice::from_ref(&proof),
            &self.environment_stack,
            "by-extension exported equality",
        )?
        .try_into()
        .map_err(|_| "by-extension effect validation changed its output arity".to_string())?;
        let Some(fact_id) = fact_id else {
            return Ok(true);
        };
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: compile the ordered proof-step Results in one inherited
    /// compiler environment, then combine the exact left-to-right and
    /// right-to-left subset child Results with the target ABI's set
    /// extensionality constructor.
    pub(super) fn construct_lean_proof_from_by_extension_stmt_result(
        &mut self,
        result: &SuccessByExtensionStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let statement = &result.statement;
        let equality: Fact = EqualFact::new(
            statement.left.clone(),
            statement.right.clone(),
            statement.line_file.clone(),
        )
        .into();
        if verification.left != statement.left.to_string()
            || verification.right != statement.right.to_string()
            || verification.prove_goal != equality.to_string()
            || verification.proof_steps.len() != statement.proof.len()
        {
            return Err("by-extension Result changed its sets, goal, or proof-step order".into());
        }
        let forward_fact: Fact = SubsetFact::new(
            statement.left.clone(),
            statement.right.clone(),
            statement.line_file.clone(),
        )
        .into();
        let backward_fact: Fact = SubsetFact::new(
            statement.right.clone(),
            statement.left.clone(),
            statement.line_file.clone(),
        )
        .into();

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let mut local_lines = Vec::new();
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                local_lines.extend(lines);
            }
            let Some(forward) = self.construct_lean_direct_subset_child_for_by_extension(
                &verification.left_to_right_check,
                &forward_fact,
                "left-to-right",
            )?
            else {
                return Ok(None);
            };
            let Some(backward) = self.construct_lean_direct_subset_child_for_by_extension(
                &verification.right_to_left_check,
                &backward_fact,
                "right-to-left",
            )?
            else {
                return Ok(None);
            };
            let left_carrier_evidence =
                render_proof_that_every_set_carrier_value_has_a_complex_representative(
                    &statement.left,
                    &self.environment_stack,
                )?;
            let right_carrier_evidence =
                render_proof_that_every_set_carrier_value_has_a_complex_representative(
                    &statement.right,
                    &self.environment_stack,
                )?;
            let proposition = render_fact(&equality, &self.environment_stack)?;
            let mut proof_lines = vec!["by".to_string()];
            proof_lines.extend(local_lines.into_iter().map(|line| indent_lines(&line, 2)));
            proof_lines.push(format!(
                "  exact Litex.Same.setExt\n    (Litex.Set.subsetFromComplexMembershipImplication ({left_carrier_evidence}) ({forward}))\n    (Litex.Set.subsetFromComplexMembershipImplication ({right_carrier_evidence}) ({backward}))"
            ));
            Ok(Some(CompiledFactProofBody {
                fact: equality,
                proposition,
                proof_expression: format!("({})", proof_lines.join("\n")),
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn construct_lean_direct_subset_child_for_by_extension(
        &mut self,
        child: &StmtResult,
        expected: &Fact,
        direction: &str,
    ) -> Result<Option<String>, String> {
        let child = child
            .factual_success()
            .ok_or_else(|| format!("by-extension {direction} child is not factual"))?;
        if child.fact().to_string() != expected.to_string() {
            return self
                .construct_lean_subset_proof_from_alpha_equivalent_forall_citation(
                    child, expected, direction,
                )
                .map(Some);
        }
        validate_scoped_fact_check_result(
            child,
            expected,
            &format!("by-extension {direction} subset child"),
        )?;
        self.construct_lean_proof_from_direct_fact_result(child)
    }

    /// `Reuse`: extension verification may request an alpha-fresh forall
    /// spelling of a subset already proved by a local statement. The exact
    /// source FactId selects the theorem; both the requested and stored forall
    /// structures are independently checked against the expected subset.
    pub(super) fn construct_lean_subset_proof_from_alpha_equivalent_forall_citation(
        &self,
        child: &SuccessFactStmtResult,
        expected_subset: &Fact,
        direction: &str,
    ) -> Result<String, String> {
        if !child.store.infers.is_empty() || child.store.fact_id.is_some() {
            return Err(format!(
                "by-extension {direction} forall check unexpectedly published effects"
            ));
        }
        validate_forall_fact_as_subset(&child.fact(), expected_subset)
            .map_err(|error| format!("by-extension {direction} requested forall: {error}"))?;
        let SuccessFactProofResult::StoredFactCitation(citation) = child.proof() else {
            return Err(format!(
                "by-extension {direction} generated forall is not an exact FactId citation"
            ));
        };
        let source_fact_id = citation.source_fact_id;
        let stored = self
            .environment_stack
            .fact_propositions
            .get(&source_fact_id)
            .ok_or_else(|| {
                format!(
                    "by-extension {direction} cites unavailable local FactId `{source_fact_id}`"
                )
            })?;
        validate_forall_fact_as_subset(stored, expected_subset)
            .map_err(|error| format!("by-extension {direction} stored forall: {error}"))?;
        self.environment_stack
            .fact_names
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "by-extension {direction} local FactId `{source_fact_id}` has no Lean binding"
                )
            })
    }

    /// `Combine`: replay one ordinary structured integer-induction Result.
    /// The base and step cases each own an inherited compiler environment;
    /// only the generated outer forall and its exact FactId survive those
    /// scopes. Strong and finite-set induction deliberately remain separate
    /// fail-closed statement families.
    pub(super) fn compile_structured_integer_induction_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByInducStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) =
            self.construct_lean_proof_from_structured_integer_induction_stmt_result(result)?
        else {
            return Ok(false);
        };
        let fact_id = validate_generated_fact_publication_effects(
            &result.common.infers,
            &proof.fact,
            "structured integer induction generated forall",
        )?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {} := {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    pub(super) fn construct_lean_proof_from_structured_integer_induction_stmt_result(
        &mut self,
        result: &SuccessByInducStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let SuccessVerifyByInducProofResult::IntegerStructured(proof) = &verification.proof else {
            return Ok(None);
        };
        if result.statement.strong || proof.strong {
            return Err(
                "structured integer-induction compiler does not yet support strong induction"
                    .into(),
            );
        }
        if is_literal_zero(&proof.start) {
            return Err(
                "structured integer induction from zero requires a sound Litex nonnegative-value to native-integer order bridge"
                    .into(),
            );
        }
        if result.statement.base_proof.is_none() || result.statement.step_proof.is_none() {
            return Err("structured integer-induction Result lost its base or step body".into());
        }
        if verification.parameter_binding != result.statement.param_binding
            || verification.parameter.to_string()
                != obj_for_bound_param_in_scope(&result.statement.param_binding).to_string()
            || verification.prove_goals.len() != result.statement.to_prove.len()
            || verification.prove_goals.is_empty()
            || verification
                .prove_goals
                .iter()
                .zip(result.statement.to_prove.iter())
                .any(|(retained, source)| {
                    retained.to_string() != source.clone().to_fact().to_string()
                })
            || proof.start.to_string() != result.statement.induc_from.to_string()
            || proof.base.proof_steps.len()
                != result
                    .statement
                    .base_proof
                    .as_ref()
                    .expect("checked above")
                    .len()
            || proof.step.proof_steps.len()
                != result
                    .statement
                    .step_proof
                    .as_ref()
                    .expect("checked above")
                    .len()
        {
            return Err(
                "structured integer-induction Result changed its parameter, goals, start, or proof-step order"
                    .into(),
            );
        }

        self.install_structured_integer_induction_iteration_occurrence_aliases(verification)?;
        self.validate_structured_integer_induction_generated_forall(verification)?;
        let target: Fact = verification.generated_forall.clone().into();
        let expected_start_membership: Fact = InFact::new(
            proof.start.clone(),
            StandardSet::Z.into(),
            result.statement.line_file.clone(),
        )
        .into();
        let start_membership_check = proof.start_in_z_check.factual_success().ok_or_else(|| {
            "structured induction start membership child is not factual".to_string()
        })?;
        if start_membership_check.fact().to_string() != expected_start_membership.to_string()
            || !start_membership_check.store.infers.is_empty()
        {
            return Err(
                "structured induction start membership child changed its target or published effects"
                    .into(),
            );
        }
        let Some(_start_membership_proof) = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                start_membership_check,
            )?
        else {
            return Err(
                "structured induction start membership has no direct recursive Result proof consumer"
                    .into(),
            );
        };
        let start_integer =
            render_integer_obj(&proof.start, &self.environment_stack).map_err(|error| {
                format!("structured induction start has no exact integer representation: {error}")
            })?;

        let motive =
            self.render_structured_integer_induction_motive(verification, "__induction_value")?;
        let Some(base) = self.compile_structured_integer_induction_base_case(
            result,
            verification,
            proof,
            &start_integer,
        )?
        else {
            return Ok(None);
        };
        let Some(step) = self.compile_structured_integer_induction_step_case(
            result,
            verification,
            proof,
            &start_integer,
        )?
        else {
            return Ok(None);
        };

        let proposition =
            render_forall_fact_type(&verification.generated_forall, &self.environment_stack)?;
        let proof_expression = format!(
            "by\n  intro __target_value __domain1\n  have __target_ge_start_real : (({start_integer}) : ℝ) ≤ (__target_value : ℝ) := by\n    simpa [Litex.Le, Litex.OrderValue] using __domain1\n  have __target_ge_start : {start_integer} ≤ __target_value := by\n    exact_mod_cast __target_ge_start_real\n  exact Litex.Rules.integerInductionFrom (motive := fun __induction_value : ℤ => {motive}) ({base}) ({step}) __target_value __target_ge_start"
        );
        Ok(Some(CompiledFactProofBody {
            fact: target,
            proposition,
            proof_expression,
        }))
    }

    pub(super) fn validate_structured_integer_induction_generated_forall(
        &self,
        verification: &SuccessVerifyByInducResult,
    ) -> Result<(), String> {
        let parameters = verification
            .generated_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        let [(generated_binding, generated_type)] = parameters.as_slice() else {
            return Err("structured induction generated forall must own one parameter".into());
        };
        if generated_type.to_string() != ParamType::Obj(StandardSet::Z.into()).to_string()
            || verification.generated_forall.dom_facts.len() != 1
            || verification.generated_forall.then_facts.len() != verification.prove_goals.len()
        {
            return Err(
                "structured induction generated forall changed its integer binder, domain, or conclusion arity"
                    .into(),
            );
        }
        let mut retained_context = self.environment_stack.clone();
        install_structured_induction_shape_symbol(
            generated_binding.id(),
            "__induction_shape",
            &mut retained_context,
        );
        let mut source_context = self.environment_stack.clone();
        install_structured_induction_shape_symbol(
            verification.parameter_binding.id(),
            "__induction_shape",
            &mut source_context,
        );
        let generated_domain = render_fact(
            &verification.generated_forall.dom_facts[0],
            &retained_context,
        )?;
        let expected_domain: Fact = GreaterEqualFact::new(
            verification.parameter.clone(),
            match &verification.proof {
                SuccessVerifyByInducProofResult::IntegerStructured(proof) => proof.start.clone(),
                _ => return Err("structured induction retained another proof family".into()),
            },
            verification.generated_forall.line_file.clone(),
        )
        .into();
        if generated_domain != render_fact(&expected_domain, &source_context)? {
            return Err("structured induction generated forall changed its lower bound".into());
        }
        for (index, (generated, expected)) in verification
            .generated_forall
            .then_facts
            .iter()
            .zip(verification.prove_goals.iter())
            .enumerate()
        {
            if render_fact(&generated.clone().to_fact(), &retained_context)?
                != render_fact(expected, &source_context)?
            {
                return Err(format!(
                    "structured induction generated forall changed conclusion {index}"
                ));
            }
        }
        Ok(())
    }

    fn install_structured_integer_induction_iteration_occurrence_aliases(
        &mut self,
        verification: &SuccessVerifyByInducResult,
    ) -> Result<(), String> {
        fn collect_from_object(
            object: &Obj,
            aggregates: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) {
            if let Obj::Sum(sum) = object {
                if let Some(occurrence_id) = sum.source_occurrence_id {
                    aggregates.push((occurrence_id, obj_equality_key(object)));
                }
            }
            let _: Result<bool, ()> = Runtime::same_shape_and_corresponding_args_match(
                object,
                object,
                &mut |child, _| {
                    collect_from_object(child, aggregates);
                    Ok(true)
                },
            );
        }

        fn collect_from_fact(
            fact: &Fact,
            aggregates: &mut Vec<(SourceObjectOccurrenceId, String)>,
        ) -> Result<(), String> {
            let arguments = match fact {
                Fact::AtomicFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ExistFact(fact) => fact.get_args_from_fact_ref(),
                Fact::OrFact(fact) => fact.get_args_from_fact_ref(),
                Fact::AndFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ChainFact(fact) => fact.get_args_from_fact_ref(),
                Fact::ForallFact(_) | Fact::ForallFactWithIff(_) | Fact::NotForall(_) => {
                    return Err(
                        "structured induction iteration aliasing does not accept a quantified goal"
                            .into(),
                    );
                }
            };
            for argument in arguments {
                collect_from_object(argument, aggregates);
            }
            Ok(())
        }

        let mut aggregates = Vec::new();
        for goal in &verification.prove_goals {
            collect_from_fact(goal, &mut aggregates)?;
        }
        aggregates.sort_by_key(|(occurrence_id, _)| occurrence_id.value());
        aggregates.dedup_by_key(|(occurrence_id, _)| occurrence_id.value());
        if aggregates.is_empty() {
            return Ok(());
        }

        let context = self
            .environment_stack
            .well_definedness
            .as_mut()
            .ok_or_else(|| {
                "structured induction aggregate goal has no active theorem WD Result".to_string()
            })?;
        for (source_occurrence_id, semantic_key) in aggregates {
            if context.iterations.contains_key(&source_occurrence_id) {
                continue;
            }
            let matching_owners = context
                .iterations
                .iter()
                .filter_map(|(owner_id, iteration)| {
                    (obj_equality_key(&iteration.source_aggregate) == semantic_key)
                        .then_some(*owner_id)
                })
                .collect::<Vec<_>>();
            let [owner_occurrence_id] = matching_owners.as_slice() else {
                return Err(format!(
                    "structured induction sum occurrence {} has {} exact theorem-WD owners",
                    source_occurrence_id.value(),
                    matching_owners.len()
                ));
            };
            if let Some(previous) = context
                .iteration_occurrence_aliases
                .insert(source_occurrence_id, *owner_occurrence_id)
            {
                if previous != *owner_occurrence_id {
                    return Err(format!(
                        "structured induction sum occurrence {} changed its WD owner",
                        source_occurrence_id.value()
                    ));
                }
            }
        }
        Ok(())
    }

    pub(super) fn render_structured_integer_induction_motive(
        &self,
        verification: &SuccessVerifyByInducResult,
        native_integer_name: &str,
    ) -> Result<String, String> {
        let mut context = self.environment_stack.clone();
        install_structured_induction_native_integer_symbol(
            verification.parameter_binding.id(),
            native_integer_name,
            &mut context,
        );
        let goals = verification
            .prove_goals
            .iter()
            .map(|goal| render_fact(goal, &context))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(conjunction(&goals))
    }

    pub(super) fn compile_structured_integer_induction_base_case(
        &mut self,
        result: &SuccessByInducStmtResult,
        verification: &SuccessVerifyByInducResult,
        proof: &SuccessVerifyByStructuredIntegerInducResult,
        start_integer: &str,
    ) -> Result<Option<String>, String> {
        let [parameter_assumption, equality_assumption] = proof.base.assumptions.as_slice() else {
            return Err(
                "structured induction base case must retain parameter and equality assumptions"
                    .into(),
            );
        };
        if parameter_assumption.role != SuccessVerifyByInducAssumptionRole::ParameterType
            || parameter_assumption.goal_index.is_some()
            || equality_assumption.role != SuccessVerifyByInducAssumptionRole::BaseCaseEquality
            || equality_assumption.goal_index.is_some()
        {
            return Err(
                "structured induction base assumptions changed their semantic roles".into(),
            );
        }
        let expected_parameter: Fact = InFact::new(
            verification.parameter.clone(),
            StandardSet::Z.into(),
            result.statement.line_file.clone(),
        )
        .into();
        let expected_equality: Fact = EqualFact::new(
            verification.parameter.clone(),
            proof.start.clone(),
            result.statement.line_file.clone(),
        )
        .into();
        if parameter_assumption.fact.to_string() != expected_parameter.to_string() {
            return Err(
                "structured induction base parameter assumption changed its proposition".into(),
            );
        }
        if equality_assumption.fact.to_string() != expected_equality.to_string() {
            return Err(
                "structured induction base equality assumption changed its proposition".into(),
            );
        }
        let parameter_fact_id_is_retained_or_inherited = infer_result_retains_fact_id(
            &proof.base.assumption_infers,
            &parameter_assumption.fact,
            parameter_assumption.fact_id,
        ) || self
            .environment_stack
            .fact_propositions
            .get(&parameter_assumption.fact_id)
            .is_some_and(|fact| fact.to_string() == parameter_assumption.fact.to_string());
        if !parameter_fact_id_is_retained_or_inherited {
            return Err(format!(
                "structured induction base parameter assumption lost FactId `{}`",
                parameter_assumption.fact_id
            ));
        }
        if !infer_result_retains_fact_id(
            &proof.base.assumption_infers,
            &equality_assumption.fact,
            equality_assumption.fact_id,
        ) {
            return Err(format!(
                "structured induction base equality assumption lost FactId `{}`",
                equality_assumption.fact_id
            ));
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            install_structured_induction_native_integer_symbol(
                verification.parameter_binding.id(),
                start_integer,
                &mut self.environment_stack,
            );
            let parameter_proof = format!("Litex.In.own Litex.Z ({start_integer})");
            self.environment_stack
                .fact_names
                .insert(parameter_assumption.fact_id, parameter_proof.clone());
            self.environment_stack.fact_propositions.insert(
                parameter_assumption.fact_id,
                parameter_assumption.fact.clone(),
            );
            let equality_proof = format!("Litex.Same.intComplex ({start_integer})");
            self.environment_stack
                .fact_names
                .insert(equality_assumption.fact_id, equality_proof);
            self.environment_stack.fact_propositions.insert(
                equality_assumption.fact_id,
                equality_assumption.fact.clone(),
            );
            let sources = vec![
                (
                    parameter_assumption.fact_id,
                    parameter_assumption.fact.clone(),
                ),
                (
                    equality_assumption.fact_id,
                    equality_assumption.fact.clone(),
                ),
            ];
            let mut lines = Vec::new();
            self.compile_typed_inference_results_as_local_have_statements(
                &proof.base.assumption_infers,
                &sources,
                &mut lines,
                "structured induction base assumptions",
            )?;
            for (index, proof_step) in proof.base.proof_steps.iter().enumerate() {
                let Some(step_lines) =
                    self.compile_stmt_result_as_local_proof_steps(proof_step, index + 1)?
                else {
                    return Err(format!(
                        "structured induction base proof step {index} has no recursive Result compiler"
                    ));
                };
                lines.extend(step_lines);
            }
            let Some(conclusion) = self.compile_structured_integer_induction_conclusions(
                &proof.base,
                verification,
                StructuredIntegerInductionConclusionPosition::Base,
            )?
            else {
                return Ok(None);
            };
            lines.push(format!("exact {conclusion}"));
            Ok(Some(format!("by\n{}", indent_lines(&lines.join("\n"), 2))))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn compile_structured_integer_induction_step_case(
        &mut self,
        _result: &SuccessByInducStmtResult,
        verification: &SuccessVerifyByInducResult,
        proof: &SuccessVerifyByStructuredIntegerInducResult,
        start_integer: &str,
    ) -> Result<Option<String>, String> {
        if proof.step.assumptions.len() != verification.prove_goals.len() + 2 {
            return Err(
                "structured induction step lost its parameter, domain, or hypothesis assumptions"
                    .into(),
            );
        }
        let parameter_assumption = &proof.step.assumptions[0];
        let domain_assumption = &proof.step.assumptions[1];
        if parameter_assumption.role != SuccessVerifyByInducAssumptionRole::ParameterType
            || parameter_assumption.goal_index.is_some()
            || domain_assumption.role != SuccessVerifyByInducAssumptionRole::DomainLowerBound
            || domain_assumption.goal_index.is_some()
        {
            return Err(
                "structured induction step assumptions changed their semantic roles".into(),
            );
        }
        let hypotheses = &proof.step.assumptions[2..];
        for (goal_index, hypothesis) in hypotheses.iter().enumerate() {
            if hypothesis.role != SuccessVerifyByInducAssumptionRole::InductionHypothesis
                || hypothesis.goal_index != Some(goal_index)
            {
                return Err(format!(
                    "structured induction hypothesis {goal_index} changed its role or goal index"
                ));
            }
        }
        for assumption in &proof.step.assumptions {
            let retained_or_inherited = infer_result_retains_fact_id(
                &proof.step.assumption_infers,
                &assumption.fact,
                assumption.fact_id,
            ) || self
                .environment_stack
                .fact_propositions
                .get(&assumption.fact_id)
                .is_some_and(|fact| fact.to_string() == assumption.fact.to_string());
            if !retained_or_inherited {
                return Err(format!(
                    "structured induction step assumption `{}` lost FactId `{}`",
                    assumption.fact, assumption.fact_id
                ));
            }
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            install_structured_induction_native_integer_symbol(
                verification.parameter_binding.id(),
                "__induction_value",
                &mut self.environment_stack,
            );
            self.environment_stack.fact_names.insert(
                parameter_assumption.fact_id,
                "Litex.In.own Litex.Z __induction_value".into(),
            );
            self.environment_stack.fact_propositions.insert(
                parameter_assumption.fact_id,
                parameter_assumption.fact.clone(),
            );
            let domain_proof = format!(
                "(by\n  have __induction_ge_start_real : (({start_integer}) : ℝ) ≤ (__induction_value : ℝ) := by\n    exact_mod_cast __induction_ge_start\n  simpa [Litex.Le, Litex.OrderValue] using __induction_ge_start_real)"
            );
            // Inference Results inside the step may retain the theorem-domain
            // FactId inherited from the enclosing forall rather than the
            // freshly introduced induction-domain FactId.  They denote the
            // same checked proposition after the exact parameter rebinding,
            // so every exact-proposition alias must point at the local proof.
            // Do not use rendered-text or shape matching here: a different
            // proposition must continue to fail closed.
            let domain_fact_aliases = self
                .environment_stack
                .fact_propositions
                .iter()
                .filter_map(|(fact_id, proposition)| {
                    (proposition.to_string() == domain_assumption.fact.to_string())
                        .then_some(*fact_id)
                })
                .collect::<Vec<_>>();
            for fact_id in domain_fact_aliases {
                self.environment_stack
                    .fact_names
                    .insert(fact_id, domain_proof.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, domain_assumption.fact.clone());
            }
            self.environment_stack
                .fact_names
                .insert(domain_assumption.fact_id, domain_proof);
            self.environment_stack
                .fact_propositions
                .insert(domain_assumption.fact_id, domain_assumption.fact.clone());
            for (goal_index, hypothesis) in hypotheses.iter().enumerate() {
                let projection =
                    conjunction_projection("__induction_hypotheses", goal_index, hypotheses.len())?;
                self.environment_stack
                    .fact_names
                    .insert(hypothesis.fact_id, projection);
                self.environment_stack
                    .fact_propositions
                    .insert(hypothesis.fact_id, hypothesis.fact.clone());
            }
            let sources = proof
                .step
                .assumptions
                .iter()
                .map(|assumption| (assumption.fact_id, assumption.fact.clone()))
                .collect::<Vec<_>>();
            // The enclosing forall may already have compiled the same typed
            // inference FactIds using its binder name.  Those proof strings
            // cannot be inherited into the induction lambda: replay the exact
            // retained inference DAG from the newly rebound assumptions.
            let mut rebound_inference_conclusions = HashSet::new();
            collect_supported_typed_infer_conclusions(
                &proof.step.assumption_infers,
                &mut rebound_inference_conclusions,
            );
            for (fact_id, proposition) in &rebound_inference_conclusions {
                if let Some(retained) = self.environment_stack.fact_propositions.get(&fact_id) {
                    if retained.to_string() != *proposition {
                        return Err(format!(
                            "structured induction step inference FactId `{fact_id}` changed its proposition"
                        ));
                    }
                }
            }
            let rebound_inference_fact_ids = rebound_inference_conclusions
                .into_iter()
                .map(|(fact_id, _)| fact_id)
                .collect::<HashSet<_>>();
            let mut lines = Vec::new();
            self.compile_typed_inference_results_as_local_have_statements_replaying_visible(
                &proof.step.assumption_infers,
                &sources,
                &mut lines,
                "structured induction step assumptions",
                &rebound_inference_fact_ids,
            )?;
            for (index, proof_step) in proof.step.proof_steps.iter().enumerate() {
                let Some(step_lines) =
                    self.compile_stmt_result_as_local_proof_steps(proof_step, index + 1)?
                else {
                    return Err(format!(
                        "structured induction step proof step {index} has no recursive Result compiler"
                    ));
                };
                lines.extend(step_lines);
            }
            let Some(conclusion) = self.compile_structured_integer_induction_conclusions(
                &proof.step,
                verification,
                StructuredIntegerInductionConclusionPosition::Step,
            )?
            else {
                return Ok(None);
            };
            lines.push(format!("exact {conclusion}"));
            Ok(Some(format!(
                "fun (__induction_value : ℤ) (__induction_ge_start : {start_integer} ≤ __induction_value) (__induction_hypotheses : {}) => by\n{}",
                self.render_structured_integer_induction_motive(
                    verification,
                    "__induction_value",
                )?,
                indent_lines(&lines.join("\n"), 2),
            )))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn compile_structured_integer_induction_conclusions(
        &mut self,
        case: &SuccessVerifyByStructuredIntegerInducCaseResult,
        verification: &SuccessVerifyByInducResult,
        position: StructuredIntegerInductionConclusionPosition,
    ) -> Result<Option<String>, String> {
        if case.conclusions.len() != verification.prove_goals.len() {
            return Err("structured induction case changed its conclusion arity".into());
        }
        let replacement = match &position {
            StructuredIntegerInductionConclusionPosition::Base => match &verification.proof {
                SuccessVerifyByInducProofResult::IntegerStructured(proof) => proof.start.clone(),
                _ => return Err("structured induction retained another proof family".into()),
            },
            StructuredIntegerInductionConclusionPosition::Step => Add::new(
                verification.parameter.clone(),
                Number::new("1".to_string()).into(),
            )
            .into(),
        };
        let mut proofs = Vec::with_capacity(case.conclusions.len());
        for (index, (conclusion, source_goal)) in case
            .conclusions
            .iter()
            .zip(verification.prove_goals.iter())
            .enumerate()
        {
            let retained = conclusion
                .check
                .factual_success()
                .ok_or_else(|| format!("structured induction conclusion {index} is not factual"))?;
            if retained.fact().to_string() != conclusion.goal.to_string()
                || !retained.store.infers.is_empty()
            {
                return Err(format!(
                    "structured induction conclusion {index} changed its checked goal or published effects"
                ));
            }
            if !fact_matches_structured_induction_goal_substitution(
                source_goal,
                &conclusion.goal,
                verification.parameter_binding.id(),
                &replacement,
            ) {
                return Err(format!(
                    "structured induction conclusion {index} is not the retained goal after the exact induction substitution"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(retained)? else {
                return Err(format!(
                    "structured induction conclusion {index} has no direct recursive Result proof consumer"
                ));
            };
            proofs.push(format!("(by simpa using ({proof}))"));
        }
        Ok(Some(if proofs.len() == 1 {
            proofs.remove(0)
        } else {
            format!("⟨{}⟩", proofs.join(", "))
        }))
    }

    pub(super) fn compile_by_enumerate_finite_set_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByEnumerateFiniteSetStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) =
            self.construct_lean_proof_from_by_enumerate_finite_set_stmt_result(result)?
        else {
            return Ok(false);
        };
        let fact_id = validate_generated_fact_publication_effects(
            &result.common.infers,
            &proof.fact,
            "by-enumerate generated forall",
        )?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {} := {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: a one-parameter finite enumeration consumes the exact
    /// resolved list-set, every frozen assignment assumption, the ordered
    /// domain/proof/conclusion children, and publishes one forall theorem.
    /// Multi-parameter products stay fail-closed until their nested branch
    /// composer uses the same assignment Result contract recursively.
    pub(super) fn construct_lean_proof_from_by_enumerate_finite_set_stmt_result(
        &mut self,
        result: &SuccessByEnumerateFiniteSetStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let statement = &result.statement;
        let source_forall = &statement.forall_fact;
        let target: Fact = source_forall.clone().into();
        let parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameters.len() != 1
            || verification.parameters.len() != 1
            || verification.parameter_sets.len() != 1
        {
            return Ok(None);
        }
        if verification.prove_goal != source_forall.to_string()
            || verification.generated_forall != target.to_string()
            || verification.parameters[0] != parameters[0].0.name()
        {
            return Err("by-enumerate Result changed its parameter or generated forall".into());
        }
        let (binding, parameter_type) = &parameters[0];
        let ParamType::Obj(source_parameter_set) = parameter_type else {
            return Ok(None);
        };
        let resolved_list_set = &verification.parameter_sets[0];
        let resolved_parameter_set: Obj = resolved_list_set.clone().into();
        if obj_equality_key(source_parameter_set) != obj_equality_key(&resolved_parameter_set) {
            // A named set resolved by equality needs that exact equality
            // FactId in this Result before membership may be transported.
            return Ok(None);
        }
        if verification.assignments.len() != resolved_list_set.list.len() {
            return Err("by-enumerate Result changed its finite assignment count".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let parameter_name = lean_identifier(binding.name());
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), parameter_name.clone())
                .is_some()
            {
                return Err("by-enumerate parameter reused its SymbolId".into());
            }
            let parameter_object = obj_for_bound_param_in_scope(binding);
            let parameter_membership: Fact = InFact::new(
                parameter_object.clone(),
                resolved_parameter_set.clone(),
                statement.line_file.clone(),
            )
            .into();
            let proposition = render_fact(&target, &self.environment_stack)?;
            let carrier_intro = if forall_parameter_uses_implicit_host_carrier(parameter_type) {
                "__carrier1 "
            } else {
                ""
            };
            let mut proof_lines = vec![
                "by".to_string(),
                format!(
                    "  intro {carrier_intro}{parameter_name} __type1{}",
                    render_forall_domain_intro_suffix(source_forall)
                ),
            ];

            if resolved_list_set.list.is_empty() {
                proof_lines.push("  rcases __type1 with ⟨__member, _⟩".into());
                proof_lines.push("  exact PEmpty.elim __member".into());
                return Ok(Some(CompiledFactProofBody {
                    fact: target,
                    proposition,
                    proof_expression: proof_lines.join("\n"),
                }));
            }

            let assignment_equalities = resolved_list_set
                .list
                .iter()
                .map(|item| {
                    Fact::from(AtomicFact::EqualFact(EqualFact::new(
                        parameter_object.clone(),
                        item.as_ref().clone(),
                        statement.line_file.clone(),
                    )))
                })
                .collect::<Vec<_>>();
            let assignment_alternatives = if assignment_equalities.len() == 1 {
                assignment_equalities[0].clone()
            } else {
                OrFact::new(
                    assignment_equalities
                        .iter()
                        .map(|fact| match fact {
                            Fact::AtomicFact(fact) => AndChainAtomicFact::AtomicFact(fact.clone()),
                            _ => unreachable!("assignment equality is atomic"),
                        })
                        .collect(),
                    statement.line_file.clone(),
                )
                .into()
            };
            let alternatives_proof = render_list_set_membership_elimination_from_fact_and_proof(
                &assignment_alternatives,
                &parameter_membership,
                "__type1",
                &self.environment_stack,
            )?;
            proof_lines.push(format!(
                "  have __assignment_cases : {} := {alternatives_proof}",
                render_fact(&assignment_alternatives, &self.environment_stack)?
            ));
            if assignment_equalities.len() == 1 {
                proof_lines.push("  have __assignment1 := __assignment_cases".into());
            } else {
                let names = (1..=assignment_equalities.len())
                    .map(|index| format!("__assignment{index}"))
                    .collect::<Vec<_>>();
                proof_lines.push(format!(
                    "  rcases __assignment_cases with {}",
                    names.join(" | ")
                ));
            }

            for (assignment_index, assignment) in verification.assignments.iter().enumerate() {
                self.environment_stack.push_inherited_environment();
                let branch = self.compile_one_by_enumerate_assignment_result(
                    source_forall,
                    assignment,
                    &assignment_equalities[assignment_index],
                    assignment_index,
                );
                self.environment_stack.pop_local_environment();
                let branch = branch?;
                if assignment_equalities.len() == 1 {
                    for line in branch.local_lines {
                        proof_lines.push(indent_lines(&line, 2));
                    }
                    proof_lines.push(format!("  exact {}", branch.exit_proof));
                } else {
                    proof_lines.push("  ·".into());
                    for line in branch.local_lines {
                        proof_lines.push(indent_lines(&line, 4));
                    }
                    proof_lines.push(format!("    exact {}", branch.exit_proof));
                }
            }
            Ok(Some(CompiledFactProofBody {
                fact: target,
                proposition,
                proof_expression: proof_lines.join("\n"),
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn compile_one_by_enumerate_assignment_result(
        &mut self,
        source_forall: &ForallFact,
        assignment: &SuccessVerifyByAssignmentResult,
        expected_equality: &Fact,
        assignment_index: usize,
    ) -> Result<CompiledFiniteAssignmentBranch, String> {
        if assignment.assignment.len() != 1 || assignment.assumptions.len() != 1 {
            return Err(format!(
                "by-enumerate assignment {assignment_index} changed its source arity"
            ));
        }
        let retained_assumption = &assignment.assumptions[0];
        if retained_assumption.fact.to_string() != expected_equality.to_string() {
            return Err(format!(
                "by-enumerate assignment {assignment_index} changed its equality assumption"
            ));
        }
        let [source_store] = retained_assumption.infers.store_fact_outputs.as_slice() else {
            return Err(format!(
                "by-enumerate assignment {assignment_index} lost its assumption store"
            ));
        };
        if source_store.fact_id != Some(retained_assumption.fact_id)
            || source_store.itself_and_why_itself_is_stored.0.to_string()
                != retained_assumption.fact.to_string()
        {
            return Err(format!(
                "by-enumerate assignment {assignment_index} changed its assumption FactId"
            ));
        }
        let assignment_name = format!("__assignment{}", assignment_index + 1);
        self.environment_stack
            .fact_names
            .insert(retained_assumption.fact_id, assignment_name);
        self.environment_stack.fact_propositions.insert(
            retained_assumption.fact_id,
            retained_assumption.fact.clone(),
        );
        let mut local_lines = Vec::new();
        self.compile_typed_inference_results_as_local_have_statements(
            &retained_assumption.infers,
            &[(
                retained_assumption.fact_id,
                retained_assumption.fact.clone(),
            )],
            &mut local_lines,
            &format!("by-enumerate assignment {assignment_index} assumption"),
        )?;

        self.compile_finite_assignment_domain_proof_and_conclusion_children(
            source_forall,
            assignment,
            assignment_index,
            local_lines,
            "by-enumerate",
        )
    }

    pub(super) fn compile_finite_assignment_domain_proof_and_conclusion_children(
        &mut self,
        source_forall: &ForallFact,
        assignment: &SuccessVerifyByAssignmentResult,
        assignment_index: usize,
        mut local_lines: Vec<String>,
        procedure_name: &str,
    ) -> Result<CompiledFiniteAssignmentBranch, String> {
        if assignment.domain_checks.len() != source_forall.dom_facts.len() {
            return Err(format!(
                "{procedure_name} assignment {assignment_index} changed its domain arity"
            ));
        }
        for (domain_index, (domain, expected)) in assignment
            .domain_checks
            .iter()
            .zip(source_forall.dom_facts.iter())
            .enumerate()
        {
            if domain.fact.to_string() != expected.to_string() {
                return Err(format!(
                    "{procedure_name} assignment {assignment_index} changed domain {domain_index}"
                ));
            }
            if !domain.satisfied {
                let negated = domain.negated_check.as_ref().ok_or_else(|| {
                    format!(
                        "{procedure_name} assignment {assignment_index} skipped without a negated domain child"
                    )
                })?;
                if domain.satisfied_infers.is_some() {
                    return Err(format!(
                        "skipped {procedure_name} domain retained store effects"
                    ));
                }
                let negated = negated.factual_success().ok_or_else(|| {
                    format!("{procedure_name} negated domain child is not factual")
                })?;
                let Some(negated_proof) =
                    self.construct_lean_proof_from_direct_fact_result(negated)?
                else {
                    return Err(format!(
                        "unsupported {procedure_name} negated domain proof Result"
                    ));
                };
                return Ok(CompiledFiniteAssignmentBranch {
                    local_lines,
                    exit_proof: format!(
                        "False.elim (({negated_proof}) __domain{})",
                        domain_index + 1
                    ),
                });
            }
            if domain.negated_check.is_some() {
                return Err(format!(
                    "satisfied {procedure_name} domain retained a negated child"
                ));
            }
            let checked = domain
                .check
                .factual_success()
                .ok_or_else(|| format!("satisfied {procedure_name} domain is not factual"))?;
            validate_scoped_fact_check_result(
                checked,
                expected,
                &format!("{procedure_name} assignment {assignment_index} domain {domain_index}"),
            )?;
            let Some(domain_proof) = self.construct_lean_proof_from_direct_fact_result(checked)?
            else {
                return Err(format!("unsupported {procedure_name} domain proof Result"));
            };
            let infers = domain.satisfied_infers.as_ref().ok_or_else(|| {
                format!("satisfied {procedure_name} domain lost its store Result")
            })?;
            let [store] = infers.store_fact_outputs.as_slice() else {
                return Err(format!(
                    "{procedure_name} domain store changed its source arity"
                ));
            };
            let fact_id = store
                .fact_id
                .ok_or_else(|| format!("{procedure_name} domain store has no FactId"))?;
            if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "{procedure_name} domain store changed its proposition"
                ));
            }
            let domain_name = format!(
                "__assignment{}_domain{}",
                assignment_index + 1,
                domain_index + 1
            );
            local_lines.push(format!(
                "have {domain_name} : {} := {domain_proof}",
                render_fact(expected, &self.environment_stack)?
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, domain_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, expected.clone());
            self.compile_typed_inference_results_as_local_have_statements(
                infers,
                &[(fact_id, expected.clone())],
                &mut local_lines,
                &format!("{procedure_name} assignment {assignment_index} domain {domain_index}"),
            )?;
        }

        for (proof_step_index, proof_step) in assignment.proof_steps.iter().enumerate() {
            let Some(lines) =
                self.compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
            else {
                return Err(format!(
                    "unsupported {procedure_name} proof-step Result at index {proof_step_index}"
                ));
            };
            local_lines.extend(lines);
        }
        if assignment.conclusion_checks.len() != source_forall.then_facts.len() {
            return Err(format!(
                "{procedure_name} assignment {assignment_index} changed its conclusion arity"
            ));
        }
        let mut conclusion_proofs = Vec::with_capacity(assignment.conclusion_checks.len());
        for (conclusion_index, (check, expected)) in assignment
            .conclusion_checks
            .iter()
            .zip(source_forall.then_facts.iter())
            .enumerate()
        {
            let expected = expected.clone().to_fact();
            let check = check.factual_success().ok_or_else(|| {
                format!(
                    "{procedure_name} assignment {assignment_index} conclusion {conclusion_index} is not factual"
                )
            })?;
            validate_scoped_fact_check_result(
                check,
                &expected,
                &format!(
                    "{procedure_name} assignment {assignment_index} conclusion {conclusion_index}"
                ),
            )?;
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(check)? else {
                return Err(format!(
                    "unsupported {procedure_name} conclusion Result at index {conclusion_index}"
                ));
            };
            conclusion_proofs.push(proof);
        }
        let exit_proof = if conclusion_proofs.len() == 1 {
            conclusion_proofs.remove(0)
        } else {
            format!("⟨{}⟩", conclusion_proofs.join(", "))
        };
        Ok(CompiledFiniteAssignmentBranch {
            local_lines,
            exit_proof,
        })
    }

    pub(super) fn compile_by_for_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByForStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_for_stmt_result(result)? else {
            return Ok(false);
        };
        let fact_id = validate_generated_fact_publication_effects(
            &result.common.infers,
            &proof.fact,
            "by-for generated forall",
        )?;
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {} := {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: one exact range-membership child is eliminated into the
    /// evaluated integer assignments retained by `SuccessVerifyByForResult`.
    /// Every assignment then installs its own Z-membership/equality FactIds
    /// before its domain, proof-step and conclusion children are compiled.
    pub(super) fn construct_lean_proof_from_by_for_stmt_result(
        &mut self,
        result: &SuccessByForStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(SuccessVerifyByForResult::Ranges(verification)) = &result.verification else {
            // Cartesian products and multi-parameter ranges need their own
            // exact nested eliminators; they remain fail-closed for now.
            return Ok(None);
        };
        let statement = &result.statement;
        let source_forall = &statement.forall_fact;
        let target: Fact = source_forall.clone().into();
        let parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameters.len() != 1 || verification.parameters.len() != 1 {
            return Ok(None);
        }
        if verification.prove_goal != source_forall.to_string()
            || verification.generated_forall != target.to_string()
        {
            return Err("by-for Result changed its goal or generated forall".into());
        }
        let (binding, parameter_type) = &parameters[0];
        let parameter_result = &verification.parameters[0];
        if parameter_result.parameter != binding.name() {
            return Err("by-for Result changed its range parameter".into());
        }
        let ParamType::Obj(source_range) = parameter_type else {
            return Ok(None);
        };
        let retained_range: Obj = match &parameter_result.range {
            ClosedRangeOrRange::Range(range) => range.clone().into(),
            ClosedRangeOrRange::ClosedRange(range) => range.clone().into(),
        };
        if obj_equality_key(source_range) != obj_equality_key(&retained_range) {
            return Err("by-for Result changed its exact source range".into());
        }
        let lowered_range = LeanTargetObjectRepresentation::lower(&retained_range)?;
        validate_by_for_range_parameter_result(parameter_result)?;
        if verification.assignments.len() != parameter_result.enumerated_values.len() {
            return Err("by-for Result changed its evaluated assignment count".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let parameter_name = lean_identifier(binding.name());
            if self
                .environment_stack
                .symbol_names
                .insert(binding.id(), parameter_name.clone())
                .is_some()
            {
                return Err("by-for parameter reused its SymbolId".into());
            }
            install_numeric_representations_from_membership(
                binding.id(),
                &lowered_range,
                &parameter_name,
                "__type1",
                &mut self.environment_stack,
            );
            let range_value = format!("(Litex.In.rep {parameter_name} __type1)");

            let proposition = render_fact(&target, &self.environment_stack)?;
            let carrier_intro = if forall_parameter_uses_implicit_host_carrier(parameter_type) {
                "__carrier1 "
            } else {
                ""
            };
            let mut proof_lines = vec![
                "by".to_string(),
                format!(
                    "  intro {carrier_intro}{parameter_name} __type1{}",
                    render_forall_domain_intro_suffix(source_forall)
                ),
            ];
            let values = &parameter_result.enumerated_values;
            let range_membership = format!("({range_value}).property");
            proof_lines.push(format!("  have __range_bounds := {range_membership}"));
            let bound_shape = match parameter_result.range {
                ClosedRangeOrRange::Range(_) => "Finset.mem_Ico",
                ClosedRangeOrRange::ClosedRange(_) => "Finset.mem_Icc",
            };
            proof_lines.push(format!("  simp only [{bound_shape}] at __range_bounds"));

            if values.is_empty() {
                proof_lines.push("  exfalso".into());
                proof_lines.push("  omega".into());
                return Ok(Some(CompiledFactProofBody {
                    fact: target,
                    proposition,
                    proof_expression: proof_lines.join("\n"),
                }));
            }

            let parameter_object = obj_for_bound_param_in_scope(binding);
            let assignment_equalities = values
                .iter()
                .map(|value| {
                    Fact::from(AtomicFact::EqualFact(EqualFact::new(
                        parameter_object.clone(),
                        Number::new(value.clone()).into(),
                        statement.line_file.clone(),
                    )))
                })
                .collect::<Vec<_>>();
            proof_lines.push(format!(
                "  have __range_value_cases : {} := by omega",
                values
                    .iter()
                    .map(|value| format!("({range_value}).val = ({value} : ℤ)"))
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ));
            let rendered_assignment_equalities = assignment_equalities
                .iter()
                .map(|equality| render_fact(equality, &self.environment_stack))
                .collect::<Result<Vec<_>, _>>()?;
            proof_lines.push(format!(
                "  have __assignment_cases : {} := by",
                values
                    .iter()
                    .zip(rendered_assignment_equalities.iter())
                    .map(|(value, equality)| {
                        format!("(({range_value}).val = ({value} : ℤ) ∧ {equality})")
                    })
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ));
            let range_numeric_same = self
                .environment_stack
                .numeric_representation_equalities
                .get(&binding.id())
                .cloned()
                .ok_or_else(|| {
                    "by-for range parameter has no exact numeric equality bridge".to_string()
                })?;
            if values.len() == 1 {
                proof_lines.push("    have __range_value_case := __range_value_cases".into());
            } else {
                proof_lines.push(format!(
                    "    rcases __range_value_cases with {}",
                    (1..=values.len())
                        .map(|index| format!("__range_value_case{index}"))
                        .collect::<Vec<_>>()
                        .join(" | ")
                ));
            }
            for (value_index, _) in values.iter().enumerate() {
                let case_name = if values.len() == 1 {
                    "__range_value_case".to_string()
                } else {
                    format!("__range_value_case{}", value_index + 1)
                };
                let equality_proof = format!(
                    "Litex.Same.trans ({range_numeric_same}) (Litex.Same.ofEq (by exact_mod_cast {case_name}))"
                );
                let case_with_assignment = format!("⟨{case_name}, {equality_proof}⟩");
                let injected = right_associated_disjunction_injection(
                    case_with_assignment,
                    value_index,
                    values.len(),
                )?;
                if values.len() == 1 {
                    proof_lines.push(format!("    exact {injected}"));
                } else {
                    proof_lines.push("    ·".into());
                    proof_lines.push(format!("      exact {injected}"));
                }
            }
            if assignment_equalities.len() == 1 {
                proof_lines.push(
                    "  rcases __assignment_cases with ⟨__range_value_case, __assignment1⟩".into(),
                );
            } else {
                proof_lines.push(format!(
                    "  rcases __assignment_cases with {}",
                    (1..=assignment_equalities.len())
                        .map(|index| {
                            format!("⟨__range_value_case{index}, __assignment{index}⟩")
                        })
                        .collect::<Vec<_>>()
                        .join(" | ")
                ));
            }
            for (assignment_index, assignment) in verification.assignments.iter().enumerate() {
                self.environment_stack.push_inherited_environment();
                let branch = self.compile_one_by_for_range_assignment_result(
                    source_forall,
                    assignment,
                    &assignment_equalities[assignment_index],
                    &parameter_result.enumerated_values[assignment_index],
                    assignment_index,
                    binding,
                    if values.len() == 1 {
                        "__range_value_case".to_string()
                    } else {
                        format!("__range_value_case{}", assignment_index + 1)
                    },
                );
                self.environment_stack.pop_local_environment();
                let branch = branch?;
                if assignment_equalities.len() == 1 {
                    for line in branch.local_lines {
                        proof_lines.push(indent_lines(&line, 2));
                    }
                    proof_lines.push(format!("  exact {}", branch.exit_proof));
                } else {
                    proof_lines.push("  ·".into());
                    for line in branch.local_lines {
                        proof_lines.push(indent_lines(&line, 4));
                    }
                    proof_lines.push(format!("    exact {}", branch.exit_proof));
                }
            }
            Ok(Some(CompiledFactProofBody {
                fact: target,
                proposition,
                proof_expression: proof_lines.join("\n"),
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn compile_one_by_for_range_assignment_result(
        &mut self,
        source_forall: &ForallFact,
        assignment: &SuccessVerifyByAssignmentResult,
        expected_equality: &Fact,
        expected_value: &str,
        assignment_index: usize,
        binding: &SymbolBinding,
        native_range_value_equality_name: String,
    ) -> Result<CompiledFiniteAssignmentBranch, String> {
        if assignment.assignment != vec![(binding.name().to_string(), expected_value.to_string())]
            || assignment.assumptions.len() != 2
        {
            return Err(format!(
                "by-for assignment {assignment_index} changed its parameter value or assumption arity"
            ));
        }
        let parameter_object = obj_for_bound_param_in_scope(binding);
        let expected_integer_membership: Fact = InFact::new(
            parameter_object,
            StandardSet::Z.into(),
            source_forall.line_file.clone(),
        )
        .into();
        let expected = [expected_integer_membership, expected_equality.clone()];
        let names = [
            format!("__assignment{}_in_z", assignment_index + 1),
            format!("__assignment{}", assignment_index + 1),
        ];
        self.environment_stack
            .runtime_resolved_numeric_comparison_rewrites
            .push(native_range_value_equality_name);
        self.environment_stack
            .runtime_resolved_numeric_substitutions
            .insert(
                binding.substitution_key(),
                Number::new(expected_value.to_string()).into(),
            );
        let mut local_lines = Vec::new();
        for (assumption_index, ((assumption, expected), name)) in assignment
            .assumptions
            .iter()
            .zip(expected.iter())
            .zip(names.iter())
            .enumerate()
        {
            if assumption.fact.to_string() != expected.to_string() {
                return Err(format!(
                    "by-for assignment {assignment_index} changed assumption {assumption_index}"
                ));
            }
            let [store] = assumption.infers.store_fact_outputs.as_slice() else {
                return Err(format!(
                    "by-for assignment {assignment_index} assumption {assumption_index} lost its source store"
                ));
            };
            if store.fact_id != Some(assumption.fact_id)
                || store.itself_and_why_itself_is_stored.0.to_string()
                    != assumption.fact.to_string()
            {
                return Err(format!(
                    "by-for assignment {assignment_index} changed assumption {assumption_index} FactId"
                ));
            }
            self.environment_stack
                .fact_names
                .insert(assumption.fact_id, name.clone());
            self.environment_stack
                .fact_propositions
                .insert(assumption.fact_id, assumption.fact.clone());
            if assumption_index == 0 {
                let numeric_equality = self
                    .environment_stack
                    .numeric_representation_equalities
                    .get(&binding.id())
                    .ok_or_else(|| {
                        format!(
                            "by-for assignment {assignment_index} lost its range numeric equality"
                        )
                    })?;
                let numeric_membership = self
                    .environment_stack
                    .numeric_representation_memberships
                    .get(&binding.id())
                    .ok_or_else(|| {
                        format!(
                            "by-for assignment {assignment_index} lost its range integer membership"
                        )
                    })?;
                local_lines.push(format!(
                    "have {name} : {} := (Litex.In.congr ({numeric_equality}) Litex.Z).mpr ({numeric_membership})",
                    render_fact(expected, &self.environment_stack)?
                ));
            }
            self.compile_typed_inference_results_as_local_have_statements(
                &assumption.infers,
                &[(assumption.fact_id, assumption.fact.clone())],
                &mut local_lines,
                &format!("by-for assignment {assignment_index} assumption {assumption_index}"),
            )?;
        }
        self.compile_finite_assignment_domain_proof_and_conclusion_children(
            source_forall,
            assignment,
            assignment_index,
            local_lines,
            "by-for",
        )
    }

    pub(super) fn compile_by_enumerate_range_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByEnumerateRangeStmtResult,
    ) -> Result<bool, String> {
        self.compile_integer_range_membership_cases_result_to_lean_source(
            &result.statement.element,
            &result.statement.range,
            &result.statement.line_file,
            &result.common,
            result.verification.as_ref(),
            "by-enumerate-range",
        )
    }

    pub(super) fn compile_by_closed_range_as_cases_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByClosedRangeAsCasesStmtResult,
    ) -> Result<bool, String> {
        self.compile_integer_range_membership_cases_result_to_lean_source(
            &result.statement.element,
            &ClosedRangeOrRange::ClosedRange(result.statement.closed_range.clone()),
            &result.statement.line_file,
            &result.common,
            result.verification.as_ref(),
            "by-closed-range-as-cases",
        )
    }

    /// `Combine`: exact membership and endpoint verification children are
    /// eliminated into the typed equality-disjunction retained by this Result.
    /// The current compiler environment supplies only names for cited facts;
    /// all range, endpoint, case-order and publication semantics remain owned
    /// by the recursive Result.
    pub(super) fn compile_integer_range_membership_cases_result_to_lean_source(
        &mut self,
        source_element: &Obj,
        source_range: &ClosedRangeOrRange,
        line_file: &LineFile,
        common: &SuccessStmtCommonResult,
        verification: Option<&SuccessVerifyByEnumerateRangeResult>,
        result_layer: &str,
    ) -> Result<bool, String> {
        let Some(verification) = verification else {
            return Ok(false);
        };
        let source_range_obj = obj_from_closed_or_half_open_range(source_range);
        let retained_range_obj = obj_from_closed_or_half_open_range(&verification.range);
        if obj_equality_key(source_element) != obj_equality_key(&verification.element)
            || obj_equality_key(&source_range_obj) != obj_equality_key(&retained_range_obj)
        {
            return Err(format!(
                "{result_layer} Result changed its element or exact range"
            ));
        }

        let expected_membership: Fact =
            InFact::new(source_element.clone(), source_range_obj, line_file.clone()).into();
        if verification.membership_fact.to_string() != expected_membership.to_string() {
            return Err(format!(
                "{result_layer} Result changed its source membership fact"
            ));
        }
        let membership_check = verification
            .membership_check
            .factual_success()
            .ok_or_else(|| format!("{result_layer} membership child is not factual"))?;
        validate_scoped_fact_check_result(
            membership_check,
            &expected_membership,
            &format!("{result_layer} membership child"),
        )?;
        let membership_proof = self
            .construct_lean_proof_from_direct_fact_result(membership_check)?
            .ok_or_else(|| format!("unsupported {result_layer} membership proof Result"))?;

        let (start, end) = closed_or_half_open_range_endpoints(source_range);
        let expected_endpoints = [
            (SuccessVerifyByEnumerateRangeEndpointPosition::Start, start),
            (SuccessVerifyByEnumerateRangeEndpointPosition::End, end),
        ];
        if verification.endpoint_checks.len() != expected_endpoints.len() {
            return Err(format!(
                "{result_layer} Result changed its endpoint-check arity"
            ));
        }
        for (endpoint_index, (retained, (expected_position, expected_endpoint))) in verification
            .endpoint_checks
            .iter()
            .zip(expected_endpoints)
            .enumerate()
        {
            let expected_fact: Fact = InFact::new(
                expected_endpoint.clone(),
                StandardSet::Z.into(),
                line_file.clone(),
            )
            .into();
            if retained.position != expected_position
                || obj_equality_key(&retained.endpoint) != obj_equality_key(expected_endpoint)
                || retained.integer_membership_fact.to_string() != expected_fact.to_string()
            {
                return Err(format!(
                    "{result_layer} Result changed endpoint {endpoint_index}"
                ));
            }
            let checked = retained.verification.factual_success().ok_or_else(|| {
                format!("{result_layer} endpoint {endpoint_index} child is not factual")
            })?;
            validate_scoped_fact_check_result(
                checked,
                &expected_fact,
                &format!("{result_layer} endpoint {endpoint_index}"),
            )?;
            self.construct_lean_proof_from_direct_fact_result(checked)?
                .ok_or_else(|| {
                    format!("unsupported {result_layer} endpoint {endpoint_index} proof Result")
                })?;
        }

        let Some(values) = literal_integer_values_for_range(source_range)? else {
            // Symbolic endpoints need their own retained evaluation Results;
            // strings or a compiler-side Runtime lookup are not substitutes.
            return Ok(false);
        };
        if values.is_empty() {
            return Err(format!("{result_layer} retained an empty successful range"));
        }
        let equality_branches = values
            .iter()
            .map(|value| {
                AndChainAtomicFact::AtomicFact(AtomicFact::EqualFact(EqualFact::new(
                    source_element.clone(),
                    Number::new(value.clone()).into(),
                    line_file.clone(),
                )))
            })
            .collect::<Vec<_>>();
        let expected_cases: Fact = if equality_branches.len() == 1 {
            equality_branches[0].clone().into()
        } else {
            OrFact::new(equality_branches, line_file.clone()).into()
        };
        if verification.generated_cases.to_string() != expected_cases.to_string() {
            return Err(format!(
                "{result_layer} Result changed its ordered generated cases"
            ));
        }
        let fact_id = validate_generated_fact_publication_effects(
            &common.infers,
            &expected_cases,
            &format!("{result_layer} generated cases"),
        )?;

        let rendered_element = render_obj(source_element, &self.environment_stack)?;
        let rendered_cases = render_fact(&expected_cases, &self.environment_stack)?;
        let member_name = "__range_member";
        let mut proof_lines = vec![
            "by".to_string(),
            format!("  let {member_name} := Litex.In.rep {rendered_element} ({membership_proof})"),
            format!("  have __range_bounds := ({member_name}).property"),
            format!(
                "  simp only [{}] at __range_bounds",
                match source_range {
                    ClosedRangeOrRange::Range(_) => "Finset.mem_Ico",
                    ClosedRangeOrRange::ClosedRange(_) => "Finset.mem_Icc",
                }
            ),
            format!(
                "  have __range_value_cases : {} := by omega",
                values
                    .iter()
                    .map(|value| format!("({member_name}).val = ({value} : ℤ)"))
                    .collect::<Vec<_>>()
                    .join(" ∨ ")
            ),
        ];
        if values.len() == 1 {
            proof_lines.push("  have __range_value_case := __range_value_cases".into());
        } else {
            proof_lines.push(format!(
                "  rcases __range_value_cases with {}",
                (1..=values.len())
                    .map(|index| format!("__range_value_case{index}"))
                    .collect::<Vec<_>>()
                    .join(" | ")
            ));
        }
        let range_same = format!(
            "Litex.Same.trans (Litex.In.same_rep {rendered_element} ({membership_proof})) (Litex.Same.subtype {member_name})"
        );
        for value_index in 0..values.len() {
            let case_name = if values.len() == 1 {
                "__range_value_case".to_string()
            } else {
                format!("__range_value_case{}", value_index + 1)
            };
            let equality_proof = format!(
                "Litex.Same.trans ({range_same}) (by simpa [{case_name}] using Litex.Same.intComplex ({member_name}).val)"
            );
            let injected =
                right_associated_disjunction_injection(equality_proof, value_index, values.len())?;
            if values.len() == 1 {
                proof_lines.push(format!("  exact {injected}"));
            } else {
                proof_lines.push("  ·".into());
                proof_lines.push(format!("    exact {injected}"));
            }
        }

        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {rendered_cases} := {}",
            proof_lines.join("\n")
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, expected_cases);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    pub(super) fn construct_lean_runtime_resolved_numeric_comparison_from_assignment_result(
        &self,
        target: &Fact,
        evidence: &RuntimeResolvedNumericComparisonBuiltinRuleEvidence,
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("Runtime-resolved comparison evidence changed its target".into());
        }
        let Fact::AtomicFact(target_atomic) = target else {
            return Err("Runtime-resolved comparison targets a non-atomic fact".into());
        };
        let Some((source_left, source_right, allow_equal)) =
            normalized_positive_order_operands(target_atomic)
        else {
            return Err(
                "Runtime-resolved assignment compiler currently supports order comparisons only"
                    .into(),
            );
        };
        let left = evidence
            .normalized_left
            .evaluate_to_normalized_decimal_number_with_result()
            .ok_or_else(|| {
                "Runtime-resolved comparison left result is not a closed number".to_string()
            })?;
        let right = evidence
            .normalized_right
            .evaluate_to_normalized_decimal_number_with_result()
            .ok_or_else(|| {
                "Runtime-resolved comparison right result is not a closed number".to_string()
            })?;
        let comparison = crate::verification::compare_number_strings(
            &left.value.normalized_value,
            &right.value.normalized_value,
        );
        if !matches!(comparison, crate::verification::NumberCompareResult::Less)
            && !(allow_equal
                && matches!(comparison, crate::verification::NumberCompareResult::Equal))
        {
            return Err("Runtime-resolved comparison retained a false numeric result".into());
        }
        let substitutions = &self
            .environment_stack
            .runtime_resolved_numeric_substitutions;
        let mut substitution_runtime = Runtime::default();
        substitution_runtime.ensure_execution_frame_for_parse();
        let evaluate_substituted = |source: &Obj| -> Result<String, String> {
            let substituted = substitution_runtime
                .inst_obj(source, substitutions, SubstitutionMode::Exact)
                .map_err(|error| {
                    format!("Runtime-resolved comparison substitution failed: {error:?}")
                })?;
            substituted
                .evaluate_to_normalized_decimal_number_with_result()
                .map(|result| result.value.normalized_value)
                .ok_or_else(|| {
                    format!(
                        "Runtime-resolved comparison operand `{source}` is not explained by the enclosing Result substitutions"
                    )
                })
        };
        if evaluate_substituted(source_left)? != left.value.normalized_value
            || evaluate_substituted(source_right)? != right.value.normalized_value
        {
            return Err(
                "Runtime-resolved comparison normal forms disagree with enclosing Result substitutions"
                    .into(),
            );
        }
        let mut rewrites = self
            .environment_stack
            .runtime_resolved_numeric_definition_names
            .clone();
        rewrites.extend(
            self.environment_stack
                .runtime_resolved_numeric_comparison_rewrites
                .iter()
                .cloned(),
        );
        if rewrites.is_empty() {
            return Err(
                "Runtime-resolved comparison is outside a definition or assignment Result"
                    .to_string(),
            );
        }
        render_fact(target, &self.environment_stack)?;
        let rewrites = rewrites.join(", ");
        if source_left.to_string() == "0" {
            let (predicate, theorem) = if allow_equal {
                ("Nonnegative", "nonnegativeOfComplexReal")
            } else {
                ("Positive", "positiveOfComplexReal")
            };
            let rendered_operand = render_obj(source_right, &self.environment_stack)?;
            let normalized_value = &right.value.normalized_value;
            return Ok(format!(
                "(by\n  exact (Litex.{predicate}.congr (Litex.Same.ofEq (by norm_num [{rewrites}] : {rendered_operand} = ((({normalized_value} : ℝ)) : ℂ)))).mpr (Litex.OrderBridge.{theorem} (r := ({normalized_value} : ℝ)) (by norm_num)))"
            ));
        }
        Ok(format!(
            "(by\n  norm_num [Litex.Lt, Litex.Le, Litex.OrderValue, {rewrites}])"
        ))
    }

    /// `Combine`: one coverage proof is replayed in every exported goal;
    /// every branch receives its own inherited compiler environment.
    pub(super) fn construct_lean_proofs_from_by_cases_stmt_result(
        &mut self,
        result: &SuccessByCasesStmtResult,
    ) -> Result<Option<Vec<CompiledFactProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if result.statement.then_facts.len() != verification.then_facts.len()
            || result.statement.cases.len() != verification.branches.len()
            || result.statement.proofs.len() != verification.branches.len()
            || result.statement.impossible_facts.len() != verification.branches.len()
            || verification.goal_well_definedness.len() != verification.then_facts.len()
        {
            return Err("by-cases Result changed its goal or branch arity".into());
        }
        for (source, retained) in result
            .statement
            .then_facts
            .iter()
            .zip(verification.then_facts.iter())
        {
            if source.to_string() != retained.to_string() {
                return Err("by-cases verification changed an exported goal".into());
            }
            if !matches!(source, Fact::AtomicFact(_)) {
                return Ok(None);
            }
        }
        for (goal, well_definedness) in verification
            .then_facts
            .iter()
            .zip(verification.goal_well_definedness.iter())
        {
            validate_atomic_fact_well_definedness_result(well_definedness, goal)?;
        }

        let coverage = verification
            .coverage_check
            .factual_success()
            .ok_or_else(|| "by-cases coverage child is not factual".to_string())?;
        let expected_coverage: Fact = OrFact::new(
            verification
                .branches
                .iter()
                .map(|branch| branch.assumption.clone())
                .collect(),
            result.statement.line_file.clone(),
        )
        .into();
        if coverage.fact().to_string() != expected_coverage.to_string()
            || !coverage.store.infers.is_empty()
        {
            return Err("by-cases coverage child changed the ordered cases".into());
        }
        let Some(coverage_proof) = self.construct_lean_proof_from_direct_fact_result(coverage)?
        else {
            return Ok(None);
        };

        let case_names = (0..verification.branches.len())
            .map(|index| format!("__case{}", index + 1))
            .collect::<Vec<_>>();
        let mut compiled_goals = Vec::with_capacity(verification.then_facts.len());
        for (goal_index, goal) in verification.then_facts.iter().enumerate() {
            let mut proof_lines = vec!["by".to_string()];
            if verification.branches.len() == 1 {
                let case_type = render_fact(
                    &verification.branches[0].assumption.clone().into(),
                    &self.environment_stack,
                )?;
                proof_lines.push(format!(
                    "  have {} : {case_type} := {coverage_proof}",
                    case_names[0]
                ));
            } else {
                proof_lines.push(format!(
                    "  rcases ({coverage_proof}) with {}",
                    case_names.join(" | ")
                ));
            }

            for (branch_index, branch) in verification.branches.iter().enumerate() {
                if branch.assumption.to_string() != result.statement.cases[branch_index].to_string()
                    || branch.proof_steps.len() != result.statement.proofs[branch_index].len()
                {
                    return Err(format!(
                        "by-cases branch {branch_index} changed its assumption or proof-step order"
                    ));
                }
                self.environment_stack.push_inherited_environment();
                let branch_compilation = (|| {
                    let case_fact: Fact = branch.assumption.clone().into();
                    let expected_components = match &branch.assumption {
                        AndChainAtomicFact::AtomicFact(_) => Vec::new(),
                        AndChainAtomicFact::AndFact(and_fact) => and_fact
                            .facts
                            .iter()
                            .cloned()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact
                            .facts()
                            .map_err(|error| format!("invalid by-cases chain assumption: {error}"))?
                            .into_iter()
                            .map(Fact::from)
                            .collect::<Vec<_>>(),
                    };
                    let stored_assumption_fact_id =
                        if matches!(&branch.assumption, AndChainAtomicFact::AndFact(_)) {
                            let (source_fact_id, component_fact_ids) =
                                validate_conjunction_store_and_component_inference_results(
                                    &branch.proof_scope.assumption_infers,
                                    &case_fact,
                                    &expected_components,
                                    "by-cases branch assumption",
                                )?;
                            let retained_component_fact_ids = branch
                                .proof_scope
                                .assumption_components
                                .iter()
                                .map(|(fact_id, _)| *fact_id)
                                .collect::<Vec<_>>();
                            if component_fact_ids != retained_component_fact_ids {
                                return Err(
                                    "by-cases branch component Result FactIds disagree".into()
                                );
                            }
                            source_fact_id
                        } else {
                            validate_single_fact_store_output(
                                &branch.proof_scope.assumption_infers,
                                &case_fact,
                                "by-cases branch assumption",
                            )?
                        };
                    if stored_assumption_fact_id != branch.assumption_fact_id {
                        return Err("by-cases branch assumption FactIds disagree".into());
                    }
                    self.environment_stack
                        .fact_names
                        .insert(branch.assumption_fact_id, case_names[branch_index].clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(branch.assumption_fact_id, case_fact.clone());

                    if expected_components.len() != branch.proof_scope.assumption_components.len() {
                        return Err("by-cases branch lost a structural assumption component".into());
                    }
                    let mut local_lines = Vec::new();
                    for (component_index, ((fact_id, retained), expected)) in branch
                        .proof_scope
                        .assumption_components
                        .iter()
                        .zip(expected_components.iter())
                        .enumerate()
                    {
                        if retained.to_string() != expected.to_string() {
                            return Err(
                                "by-cases branch changed a structural component position".into()
                            );
                        }
                        let component_name = format!(
                            "__case{}_component{}",
                            branch_index + 1,
                            component_index + 1
                        );
                        let component_type = render_fact(retained, &self.environment_stack)?;
                        let component_proof = conjunction_projection(
                            &format!("({})", case_names[branch_index]),
                            component_index,
                            expected_components.len(),
                        )?;
                        local_lines.push(format!(
                            "have {component_name} : {component_type} := by\n  exact {component_proof}"
                        ));
                        self.environment_stack
                            .fact_names
                            .insert(*fact_id, component_name);
                        self.environment_stack
                            .fact_propositions
                            .insert(*fact_id, retained.clone());
                    }
                    for (proof_step_index, proof_step) in branch.proof_steps.iter().enumerate() {
                        let Some(lines) = self.compile_stmt_result_as_local_proof_steps(
                            proof_step,
                            proof_step_index + 1,
                        )?
                        else {
                            return Ok(None);
                        };
                        local_lines.extend(lines);
                    }

                    let exit_proof = match &branch.exit {
                        SuccessVerifyByCaseBranchExitResult::Conclusions(exit) => {
                            if result.statement.impossible_facts[branch_index].is_some()
                                || exit.checks.len() != verification.then_facts.len()
                            {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its conclusion exit"
                                ));
                            }
                            let conclusion =
                                exit.checks[goal_index].factual_success().ok_or_else(|| {
                                    format!(
                                        "by-cases branch {branch_index} conclusion is not factual"
                                    )
                                })?;
                            if conclusion.fact().to_string() != goal.to_string() {
                                return Err(format!(
                                    "by-cases branch {branch_index} conclusion changed goal `{goal}` to `{}`",
                                    conclusion.fact()
                                ));
                            }
                            validate_scoped_fact_check_result(
                                conclusion,
                                goal,
                                &format!("by-cases branch {branch_index} conclusion"),
                            )?;
                            let Some(proof) =
                                self.construct_lean_proof_from_direct_fact_result(conclusion)?
                            else {
                                return Ok(None);
                            };
                            proof
                        }
                        SuccessVerifyByCaseBranchExitResult::Contradiction(exit) => {
                            let Some(expected_impossible) =
                                &result.statement.impossible_facts[branch_index]
                            else {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its contradiction exit"
                                ));
                            };
                            if exit.impossible_fact.to_string() != expected_impossible.to_string() {
                                return Err(format!(
                                    "by-cases branch {branch_index} changed its impossible fact"
                                ));
                            }
                            let Some(contradiction) = self
                                .construct_lean_contradiction_from_result(
                                    &exit.impossible_fact,
                                    &exit.contradiction,
                                )?
                            else {
                                return Ok(None);
                            };
                            format!("False.elim ({contradiction})")
                        }
                    };
                    Ok(Some((local_lines, exit_proof)))
                })();
                self.environment_stack.pop_local_environment();
                let Some((local_lines, exit_proof)) = branch_compilation? else {
                    return Ok(None);
                };
                if verification.branches.len() == 1 {
                    for line in local_lines {
                        proof_lines.push(indent_lines(&line, 2));
                    }
                    proof_lines.push(format!("  exact {exit_proof}"));
                } else {
                    proof_lines.push("  ·".into());
                    for line in local_lines {
                        proof_lines.push(indent_lines(&line, 4));
                    }
                    proof_lines.push(format!("    exact {exit_proof}"));
                }
            }
            let proposition = self.render_fact_using_well_definedness_result(
                &verification.goal_well_definedness[goal_index],
                goal,
            )?;
            compiled_goals.push(CompiledFactProofBody {
                fact: goal.clone(),
                proposition,
                proof_expression: format!("({})", proof_lines.join("\n")),
            });
        }
        Ok(Some(compiled_goals))
    }

    pub(super) fn compile_by_contra_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByContraStmtResult,
    ) -> Result<bool, String> {
        let Some(proof) = self.construct_lean_proof_from_by_contra_stmt_result(result)? else {
            return Ok(false);
        };
        let [fact_id] = validate_compiled_fact_proof_effects(
            &result.common.infers,
            std::slice::from_ref(&proof),
            &self.environment_stack,
            "by-contra exported goal",
        )?
        .try_into()
        .map_err(|_| "by-contra effect validation changed its output arity".to_string())?;
        let Some(fact_id) = fact_id else {
            return Ok(true);
        };
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n  exact {}",
            proof.proposition, proof.proof_expression
        ));
        self.environment_stack
            .fact_names
            .insert(fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(fact_id, proof.fact);
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: install the exact reverse-assumption FactId in one inherited
    /// environment, compile the ordered proof-step Results, then combine the
    /// two retained contradiction checks.
    pub(super) fn construct_lean_proof_from_by_contra_stmt_result(
        &mut self,
        result: &SuccessByContraStmtResult,
    ) -> Result<Option<CompiledFactProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.to_prove.to_string() != result.statement.to_prove.to_string()
            || verification.proof_steps.len() != result.statement.proof.len()
            || verification.impossible_fact.to_string()
                != result.statement.impossible_fact.to_string()
            || !verification.proof_scope.assumption_components.is_empty()
        {
            return Err("by-contra Result changed its target or proof structure".into());
        }
        let Fact::AtomicFact(target_atomic) = &verification.to_prove else {
            return Ok(None);
        };
        let expected_reverse: Fact = target_atomic
            .logical_negation()
            .map_err(|_| "by-contra target has no atomic negation".to_string())?
            .into();
        if verification.reverse_assumption.to_string() != expected_reverse.to_string() {
            return Err("by-contra Result changed its reverse assumption".into());
        }
        let stored_reverse_fact_id = validate_single_fact_store_output(
            &verification.proof_scope.assumption_infers,
            &verification.reverse_assumption,
            "by-contra reverse assumption",
        )?;
        if stored_reverse_fact_id != verification.reverse_assumption_fact_id {
            return Err("by-contra reverse-assumption FactIds disagree".into());
        }
        self.environment_stack.push_inherited_environment();
        let compilation: Result<Option<String>, String> = (|| {
            self.environment_stack
                .fact_names
                .insert(verification.reverse_assumption_fact_id, "__reverse".into());
            self.environment_stack.fact_propositions.insert(
                verification.reverse_assumption_fact_id,
                verification.reverse_assumption.clone(),
            );
            let mut local_lines = Vec::new();
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                local_lines.extend(lines);
            }
            let Some(contradiction) = self.construct_lean_contradiction_from_result(
                &verification.impossible_fact,
                &verification.contradiction,
            )?
            else {
                return Ok(None);
            };
            let mut proof_lines = vec!["by".to_string(), "  classical".to_string()];
            if atomic_fact_is_logically_negated(target_atomic) {
                let reverse_type =
                    render_fact(&verification.reverse_assumption, &self.environment_stack)?;
                proof_lines
                    .push("  exact Classical.byContradiction (fun __negated_goal => by".into());
                proof_lines.push(format!(
                    "    have __reverse : {reverse_type} := Classical.byContradiction (fun __not_reverse => __negated_goal __not_reverse)"
                ));
                for line in local_lines {
                    proof_lines.push(indent_lines(&line, 4));
                }
                proof_lines.push(format!("    exact {contradiction})"));
            } else {
                proof_lines.push("  by_contra __reverse".into());
                for line in local_lines {
                    proof_lines.push(indent_lines(&line, 2));
                }
                proof_lines.push(format!("  exact {contradiction}"));
            }
            Ok(Some(format!("({})", proof_lines.join("\n"))))
        })();
        self.environment_stack.pop_local_environment();
        let Some(proof_expression) = compilation? else {
            return Ok(None);
        };
        Ok(Some(CompiledFactProofBody {
            fact: verification.to_prove.clone(),
            proposition: render_fact(&verification.to_prove, &self.environment_stack)?,
            proof_expression,
        }))
    }

    pub(super) fn construct_lean_contradiction_from_result(
        &mut self,
        impossible_fact: &AtomicFact,
        contradiction: &SuccessVerifyContradictionResult,
    ) -> Result<Option<String>, String> {
        let impossible = contradiction
            .impossible_check
            .factual_success()
            .ok_or_else(|| "contradiction positive child is not factual".to_string())?;
        let negated = contradiction
            .negated_impossible_check
            .factual_success()
            .ok_or_else(|| "contradiction negated child is not factual".to_string())?;
        let impossible_target: Fact = impossible_fact.clone().into();
        let expected_negated: Fact = impossible_fact
            .logical_negation()
            .map_err(|_| "contradiction fact has no atomic negation".to_string())?
            .into();
        if impossible.fact().to_string() != impossible_target.to_string()
            || negated.fact().to_string() != expected_negated.to_string()
            || !impossible.store.infers.is_empty()
            || !negated.store.infers.is_empty()
        {
            return Err("contradiction Result changed one of its complementary facts".into());
        }
        let Some(impossible_proof) =
            self.construct_lean_proof_from_direct_fact_result(impossible)?
        else {
            return Ok(None);
        };
        let Some(negated_proof) = self.construct_lean_proof_from_direct_fact_result(negated)?
        else {
            return Ok(None);
        };
        if atomic_fact_is_logically_negated(impossible_fact) {
            let impossible_type = render_fact(&impossible_target, &self.environment_stack)?;
            Ok(Some(format!(
                "(({impossible_proof} : {impossible_type}) ({negated_proof}))"
            )))
        } else {
            let negated_type = render_fact(&expected_negated, &self.environment_stack)?;
            Ok(Some(format!(
                "(({negated_proof} : {negated_type}) ({impossible_proof}))"
            )))
        }
    }
}
