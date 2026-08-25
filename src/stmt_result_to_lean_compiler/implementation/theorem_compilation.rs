use super::*;

impl StmtResultToLeanCompiler {
    pub(super) fn compile_sketch_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessSketchStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("a `sketch` unexpectedly exported facts to its parent environment".into());
        }
        let proof = result.proof.as_ref().ok_or_else(|| {
            "a successful `sketch` retained no recursive proof result".to_string()
        })?;
        if !proof.proof_scope.assumption_infers.is_empty()
            || !proof.proof_scope.assumption_components.is_empty()
        {
            return Err("a `sketch` retained unexpected local assumptions".into());
        }
        if proof.proof_steps.len() != result.statement.proof.len() {
            return Err("a `sketch` result changed its source proof-step order".into());
        }

        let nested_declarations =
            self.compile_stmt_results_in_new_local_environment(&proof.proof_steps)?;
        self.next_sketch_namespace_index += 1;
        let namespace = format!("__Sketch{:02}", self.next_sketch_namespace_index);
        self.declarations.push(format!(
            "namespace {namespace}\n\n{}\n\nend {namespace}",
            nested_declarations.join("\n\n")
        ));
        Ok(())
    }

    /// `Combine`: compile each retained proof-step Result inside one inherited
    /// compiler environment, then wrap the retained conclusion proof in the
    /// persistent theorem introduced by `claim`.
    pub(super) fn compile_claim_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessClaimStmtResult,
    ) -> Result<bool, String> {
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &result.verification else {
            return Ok(false);
        };
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            verification,
        )?
        else {
            return Ok(false);
        };

        if !result.common.infers.rule_applications.is_empty()
            || result.common.infers.store_fact_outputs.len() != 1
        {
            return Err("ordinary `claim` must retain exactly one outer store effect".into());
        }
        let stored = &result.common.infers.store_fact_outputs[0];
        if stored.itself_and_why_itself_is_stored.0.to_string() != verification.fact.to_string()
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
            .insert(fact_id, verification.fact.clone());
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: an `example` owns the same recursive proof body as a claim,
    /// but intentionally publishes neither a FactId nor an outer environment
    /// effect.
    pub(super) fn compile_example_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessExampleStmtResult,
    ) -> Result<bool, String> {
        let Some(SuccessVerifyClaimResult::Fact(verification)) = &result.verification else {
            return Ok(false);
        };
        if !result.common.infers.is_empty() {
            return Err("an ordinary `example` unexpectedly exported environment effects".into());
        }
        let Some(mut body) = self.compile_ordinary_fact_goal_proof_body(
            &result.statement.fact,
            result.statement.proof.len(),
            verification,
        )?
        else {
            return Ok(false);
        };

        body.local_proof_lines
            .push(format!("exact {}", body.conclusion_proof));
        self.declarations.push(format!(
            "example : {} := by\n{}",
            body.proposition,
            indent_lines(&body.local_proof_lines.join("\n"), 2)
        ));
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: read the theorem's binder WD, proof-scope assumptions,
    /// ordered proof steps, conclusion checks, and outer store directly. This
    /// first binder-bearing tranche accepts ordinary object parameters with
    /// reviewed standard-set carriers. Other binder representations remain on
    /// the explicit compatibility path.
    pub(super) fn compile_named_theorem_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        if verification.name != result.statement.name
            || verification.forall_fact.to_string() != result.statement.forall_fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Err("named theorem Result changed its declaration or proof-step order".into());
        }
        self.compile_named_forall_statement_result_to_lean_source(
            NamedForallStatementResultCompilationInput {
                name: &verification.name,
                forall_fact: &verification.forall_fact,
                well_definedness: &verification.well_definedness,
                proof_scope_assumption_infers: &verification.proof_scope.assumption_infers,
                proof_scope_assumption_components: &verification.proof_scope.assumption_components,
                proof_steps: &verification.proof_steps,
                conclusion_checks: verification.conclusion_checks.iter().collect(),
                outer_statement_common: Some(&result.common),
            },
        )
    }

    /// `Combine`: a strategy definition has the same proof-producing forall
    /// body as a named theorem. The generated Lean declaration is the proved
    /// forall fact stored by the statement. The recursive Result owns the
    /// local WD, assumptions, proof steps, and conclusion checks.
    pub(super) fn compile_strategy_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefStrategyStmtResult,
    ) -> Result<(), String> {
        let Some(verification) = &result.verification else {
            return Err(
                "StmtResultToLeanCompiler cannot compile a trusted-only strategy definition".into(),
            );
        };
        if verification.name != result.statement.name
            || verification.forall_fact.to_string() != result.statement.forall_fact.to_string()
            || verification.proof_steps.len() != result.statement.prove_process.len()
        {
            return Err("strategy Result changed its declaration or proof-step order".into());
        }
        if self.compile_named_forall_statement_result_to_lean_source(
            NamedForallStatementResultCompilationInput {
                name: &verification.name,
                forall_fact: &verification.forall_fact,
                well_definedness: &verification.well_definedness,
                proof_scope_assumption_infers: &verification.proof_scope.assumption_infers,
                proof_scope_assumption_components: &verification.proof_scope.assumption_components,
                proof_steps: &verification.proof_steps,
                conclusion_checks: verification.conclusion_checks.iter().collect(),
                outer_statement_common: Some(&result.common),
            },
        )? {
            Ok(())
        } else {
            Err("StmtResultToLeanCompiler does not support this strategy proof Result shape".into())
        }
    }

    /// `PassThrough`: a setting is a Litex elaboration declaration. Every use
    /// has already expanded to ordinary fresh binders and premise facts before
    /// execution produces later Results, so no setting binding belongs in the
    /// Lean-generation environment stack.
    pub(super) fn compile_setting_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefSettingStmtResult,
    ) -> Result<(), String> {
        if !result.common.infers.is_empty() {
            return Err("setting definition unexpectedly published mathematical effects".into());
        }
        if result.statement.name.is_empty() {
            return Err("setting definition retained an empty source name".into());
        }
        Ok(())
    }

    pub(super) fn compile_template_definition_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessDefTemplateStmtResult,
    ) -> Result<(), String> {
        if !result.statement.template_arg_dom.is_empty()
            || !result.template_domain_results.is_empty()
        {
            return Err(
                "direct Template compiler currently supports no template domain clauses".into(),
            );
        }
        let source_parameters = result
            .statement
            .template_arg_def
            .collect_param_bindings_with_types();
        if source_parameters.is_empty()
            || source_parameters
                .iter()
                .any(|(_, parameter_type)| !matches!(parameter_type, ParamType::Set(_)))
        {
            return Err(
                "direct Template compiler currently supports only one or more `set` parameters"
                    .into(),
            );
        }
        if result.template_parameter_groups.len() != result.statement.template_arg_def.len() {
            return Err("Template Result changed its parameter-group count".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let mut parameter_binders = Vec::with_capacity(source_parameters.len());
            for (group_index, (source_group, retained_group)) in result
                .statement
                .template_arg_def
                .iter()
                .zip(result.template_parameter_groups.iter())
                .enumerate()
            {
                if retained_group.group_index != group_index
                    || !matches!(source_group.param_type, ParamType::Set(_))
                    || !matches!(retained_group.parameter_type, ParamType::Set(_))
                    || retained_group.carrier.is_some()
                    || retained_group.parameters.len() != source_group.params.len()
                {
                    return Err(format!(
                        "Template parameter group {group_index} changed its set-binder Result shape"
                    ));
                }
                for (parameter_index, (binding, premise)) in source_group
                    .params
                    .iter()
                    .zip(retained_group.parameters.iter())
                    .enumerate()
                {
                    if premise.symbol_id != Some(binding.id())
                        || !matches!(
                            premise.role,
                            WellDefinedBinderPremiseRole::ParameterMembership {
                                parameter_group_index,
                                parameter_index: retained_parameter_index,
                            } if parameter_group_index == group_index
                                && retained_parameter_index == parameter_index
                        )
                    {
                        return Err(format!(
                            "Template parameter {group_index}:{parameter_index} changed its Result-owned identity or role"
                        ));
                    }
                    validate_set_parameter_premise(binding.id(), &premise.proposition)?;
                    let fact_id = fact_id_for_well_definedness_binder_premise(premise)?;
                    let lean_name = lean_identifier(binding.name());
                    self.environment_stack
                        .symbol_names
                        .insert(binding.id(), lean_name.clone());
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, "True.intro".into());
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, premise.proposition.clone());
                    parameter_binders.push(format!("({lean_name} : Litex.Set)"));
                }
            }

            let SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveObjEqualStmt(body)) =
                result.body_statement_result.as_ref()
            else {
                return Err(
                    "direct Template compiler currently supports only a `have <name> set = <value>` body"
                        .into(),
                );
            };
            let bindings = body.statement.param_def.collect_param_bindings_with_types();
            let [(defined_binding, defined_type @ ParamType::Set(_))] = bindings.as_slice() else {
                return Err(
                    "direct Template compiler requires its body to define exactly one set alias"
                        .into(),
                );
            };
            let [value] = body.statement.objs_equal_to.as_slice() else {
                return Err("direct Template compiler requires exactly one set-alias value".into());
            };
            if defined_binding.name() != result.statement.template_name {
                return Err("Template name changed between its header and body Result".into());
            }
            let verification = body.verification.as_ref().ok_or_else(|| {
                "Template body has no structured set-value type-check Result".to_string()
            })?;
            let [type_check] = verification.type_checks.as_slice() else {
                return Err("Template set-alias body changed its type-check count".into());
            };
            let expected_type = object_type_fact_for_compiler_definition(
                value.clone(),
                defined_type,
                body.statement.line_file.clone(),
            );
            let factual_type_check = type_check.factual_success().ok_or_else(|| {
                "Template set-alias body type check is not a successful fact Result".to_string()
            })?;
            if factual_type_check.fact().to_string() != expected_type.to_string() {
                return Err("Template set-alias body changed its value type-check fact".into());
            }
            let SuccessFactProofResult::BuiltinRule(type_check_proof) = factual_type_check.proof()
            else {
                return Err(
                    "Template set-alias body type check changed from its direct builtin Result"
                        .into(),
                );
            };
            if type_check_proof.evidence.is_typed()
                || !type_check_proof.subgoals.is_empty()
                || factual_type_check.fact_id.is_some()
                || !factual_type_check.infers.is_empty()
            {
                return Err(
                    "Template set-alias body type check retained unexpected evidence, children, or stores"
                        .into(),
                );
            }

            let defined_object: Obj =
                Identifier::new_bound(defined_binding.name().to_string(), defined_binding.as_ref())
                    .into();
            let expected_stores = vec![
                object_type_fact_for_compiler_definition(
                    defined_object.clone(),
                    defined_type,
                    body.statement.line_file.clone(),
                ),
                EqualFact::new(
                    defined_object,
                    value.clone(),
                    body.statement.line_file.clone(),
                )
                .into(),
            ];
            exact_ordered_fact_ids_from_store_results(
                &body.common.infers,
                &expected_stores,
                "Template set-alias body",
            )?;
            if body.common.infers.store_fact_outputs.iter().any(|output| {
                !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty()
            }) {
                return Err(
                    "Template set-alias body retained unsupported inferred consequences".into(),
                );
            }
            let lowered_value = LeanTargetObjectRepresentation::lower(value)?;
            let rendered_value =
                render_set_definition_value(&lowered_value, &self.environment_stack)?;
            Ok((
                parameter_binders,
                lean_identifier(&result.statement.template_name),
                rendered_value,
            ))
        })();
        self.environment_stack.pop_local_environment();
        let (parameter_binders, lean_name, rendered_value) = compilation?;
        if self
            .environment_stack
            .template_set_alias_bindings
            .insert(
                result.statement.template_name.clone(),
                TemplateSetAliasBinding {
                    lean_name: lean_name.clone(),
                    parameter_count: source_parameters.len(),
                },
            )
            .is_some()
        {
            return Err(format!(
                "duplicate compiler Template binding `{}`",
                result.statement.template_name
            ));
        }
        self.declarations.push(format!(
            "abbrev {lean_name} {} := {rendered_value}",
            parameter_binders.join(" ")
        ));
        Ok(())
    }

    /// `Combine`: compile the exact forall proof owned by a successful
    /// `by reflexive_prop`/`symmetric_prop`/`transitive_prop`/
    /// `antisymmetric_prop` Result, then remember the generated theorem only
    /// in the active compiler environment. The registration is not a stored
    /// Litex fact, so it deliberately has no fabricated FactId.
    pub(super) fn compile_registered_predicate_property_stmt_result_to_lean_source(
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
        let forall_check = verification.forall_check.factual_success().ok_or_else(|| {
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
                well_definedness: &verification.well_definedness,
                proof_scope_assumption_infers: &verification.assumption_infers,
                proof_scope_assumption_components: &[],
                proof_steps: &verification.proof_steps,
                conclusion_checks,
                outer_statement_common: None,
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

    pub(super) fn compile_named_forall_statement_result_to_lean_source(
        &mut self,
        verification: NamedForallStatementResultCompilationInput<'_>,
    ) -> Result<bool, String> {
        let parameters = verification
            .forall_fact
            .typed_parameters
            .collect_param_bindings_with_types();
        if parameters.iter().any(|(_, parameter_type)| {
            !matches!(parameter_type, ParamType::Set(_) | ParamType::Obj(_))
        }) || verification
            .forall_fact
            .then_facts
            .iter()
            .any(|conclusion| {
                !fact_is_supported_by_direct_named_theorem(&conclusion.clone().to_fact())
            })
        {
            return Ok(false);
        }
        if verification.conclusion_checks.len() != verification.forall_fact.then_facts.len() {
            return Err("named forall Result changed its conclusion child order".into());
        }
        if verification.forall_fact.then_facts.is_empty() {
            return Err("named forall Result retained no conclusions".into());
        }
        if !verification.proof_scope_assumption_components.is_empty() {
            return Ok(false);
        }
        let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(well_definedness)) =
            verification.well_definedness.recursive.as_deref()
        else {
            return Err("named forall Result has no recursive forall well-definedness".into());
        };
        let well_defined_parameters = well_definedness
            .binder
            .parameter_groups
            .iter()
            .flat_map(|group| {
                group
                    .parameters
                    .iter()
                    .map(move |parameter| (group, parameter))
            })
            .collect::<Vec<_>>();
        if well_definedness.statement.to_string() != verification.forall_fact.to_string()
            || well_definedness.premises.len() != verification.forall_fact.dom_facts.len()
            || well_defined_parameters.len() != parameters.len()
            || well_definedness.conclusions.len() != verification.forall_fact.then_facts.len()
        {
            return Err("named forall well-definedness changed its forall structure".into());
        }
        for (parameter_index, ((binding, parameter_type), (group, parameter))) in parameters
            .iter()
            .zip(well_defined_parameters.iter())
            .enumerate()
        {
            if group.group_index >= well_definedness.binder.parameter_groups.len()
                || group.parameter_type.to_string() != parameter_type.to_string()
                || parameter.symbol_id != Some(binding.id())
            {
                return Err(format!(
                    "named forall binder parameter {parameter_index} changed its type or SymbolId"
                ));
            }
            match parameter_type {
                ParamType::Set(_) => {
                    validate_set_parameter_premise(binding.id(), &parameter.proposition)?;
                }
                ParamType::Obj(expected_set) => {
                    validate_object_parameter_premise(
                        binding.id(),
                        expected_set,
                        &parameter.proposition,
                    )?;
                }
                ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    unreachable!("refined set parameters were excluded above")
                }
            }
            validate_atomic_fact_well_definedness_result(
                parameter.well_definedness.as_ref(),
                &parameter.proposition,
            )?;
            validate_single_fact_store_output(
                &parameter.infers,
                &parameter.proposition,
                "named forall binder WD",
            )?;
        }
        for (conclusion_index, (conclusion, expected)) in well_definedness
            .conclusions
            .iter()
            .zip(verification.forall_fact.then_facts.iter())
            .enumerate()
        {
            let expected = expected.clone().to_fact();
            if conclusion.proposition.to_string() != expected.to_string() {
                return Err(format!(
                    "named forall WD conclusion {conclusion_index} changed its proposition"
                ));
            }
            validate_direct_named_theorem_conclusion_well_definedness(
                conclusion.well_definedness.as_ref(),
                &conclusion.proposition,
            )?;
            validate_success_store_fact_result_allowing_well_definedness_inferred_children(
                &conclusion.store,
                &conclusion.proposition,
                "named forall conclusion WD",
            )?;
        }
        for (premise_index, (premise, expected)) in well_definedness
            .premises
            .iter()
            .zip(verification.forall_fact.dom_facts.iter())
            .enumerate()
        {
            if premise.proposition.to_string() != expected.to_string() {
                return Err(format!(
                    "named forall WD premise {premise_index} changed its proposition"
                ));
            }
            validate_direct_named_theorem_conclusion_well_definedness(
                premise.well_definedness.as_ref(),
                &premise.proposition,
            )?;
            validate_success_store_fact_result_allowing_well_definedness_inferred_children(
                &premise.store,
                &premise.proposition,
                "named forall premise WD",
            )?;
        }

        let theorem_fact: Fact = (*verification.forall_fact).clone().into();
        let theorem_fact_id =
            if let Some(outer_statement_common) = verification.outer_statement_common {
                if !outer_statement_common.infers.rule_applications.is_empty()
                    || outer_statement_common.infers.store_fact_outputs.len() > 1
                {
                    return Ok(false);
                }
                let [stored] = outer_statement_common.infers.store_fact_outputs.as_slice() else {
                    return Err("named forall Result has no outer store effect".into());
                };
                if stored.itself_and_why_itself_is_stored.0.to_string() != theorem_fact.to_string()
                    || !stored.inferred_facts.is_empty()
                    || !stored.inferred_fact_ids.is_empty()
                {
                    return Ok(false);
                }
                Some(
                    stored
                        .fact_id
                        .ok_or_else(|| "named forall outer store has no FactId".to_string())?,
                )
            } else {
                None
            };

        if verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Ok(false);
        }
        let parameter_facts = well_defined_parameters
            .iter()
            .map(|(_, parameter)| parameter.proposition.clone())
            .collect::<Vec<_>>();
        let mut assumption_facts = parameter_facts.clone();
        assumption_facts.extend(verification.forall_fact.dom_facts.iter().cloned());
        let assumption_fact_ids = exact_ordered_fact_ids_from_store_results(
            verification.proof_scope_assumption_infers,
            &assumption_facts,
            "named forall proof-scope assumptions",
        )?;
        let (parameter_fact_ids, premise_fact_ids) =
            assumption_fact_ids.split_at(parameter_facts.len());
        if verification
            .proof_scope_assumption_infers
            .store_fact_outputs
            .iter()
            .take(parameter_facts.len())
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
        {
            return Ok(false);
        }

        self.environment_stack.push_inherited_environment();
        let compilation: Result<Option<CompiledNamedForallStatementProofBody>, String> = (|| {
            let mut binder_declarations = Vec::new();
            let mut binder_intro_names = Vec::new();
            for (parameter_index, (((binding, parameter_type), parameter), fact_id)) in parameters
                .iter()
                .zip(parameter_facts.iter())
                .zip(parameter_fact_ids.iter())
                .enumerate()
            {
                let parameter_name = lean_identifier(binding.name());
                if self
                    .environment_stack
                    .symbol_names
                    .insert(binding.id(), parameter_name.clone())
                    .is_some()
                {
                    return Err(format!(
                        "named forall binder reused SymbolId `{:?}`",
                        binding.id()
                    ));
                }
                if matches!(parameter_type, ParamType::Set(_)) {
                    validate_set_parameter_premise(binding.id(), parameter)?;
                    binder_declarations.push(format!("({parameter_name} : Litex.Set)"));
                    binder_intro_names.push(parameter_name);
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, "True.intro".to_string());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, parameter.clone());
                    continue;
                }

                let parameter_set = parameter_set(parameter_type)
                    .map_err(|error| format!("named forall binder {parameter_index}: {error}"))?;
                let rendered_parameter_set = render_obj(parameter_set, &self.environment_stack)?;
                let carrier_name = format!(
                    "__carrier{}_{}",
                    self.next_fact_name_index,
                    parameter_index + 1
                );
                match parameter_set {
                    Obj::FnSet(_) => {
                        binder_declarations.push(format!("{{{carrier_name} : Type 1}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                    set if set_requires_heterogeneous_carrier(set) => {
                        binder_declarations.push(format!("{{{carrier_name} : Type}}"));
                        binder_intro_names.push(carrier_name.clone());
                        binder_declarations.push(format!("({parameter_name} : {carrier_name})"));
                    }
                    _ => binder_declarations.push(format!("({parameter_name} : ℂ)")),
                }
                binder_intro_names.push(parameter_name.clone());
                let rendered_parameter_fact = render_fact(parameter, &self.environment_stack)?;
                let expected_parameter_fact =
                    format!("Litex.In {parameter_name} {rendered_parameter_set}");
                if rendered_parameter_fact != expected_parameter_fact {
                    return Err(format!(
                        "named forall parameter evidence mismatch: expected `{expected_parameter_fact}`, found `{rendered_parameter_fact}`"
                    ));
                }
                let hypothesis_name =
                    format!("__h{}_{}", self.next_fact_name_index, parameter_index + 1);
                binder_declarations
                    .push(format!("({hypothesis_name} : {rendered_parameter_fact})"));
                binder_intro_names.push(hypothesis_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(*fact_id, hypothesis_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*fact_id, parameter.clone());
                install_parameter_fact_aliases(
                    binding.id(),
                    parameter,
                    &hypothesis_name,
                    parameter_set,
                    &mut self.environment_stack,
                )?;
            }

            for (premise_index, (((premise, premise_fact_id), premise_output), premise_wd)) in
                verification
                    .forall_fact
                    .dom_facts
                    .iter()
                    .zip(premise_fact_ids.iter())
                    .zip(
                        verification
                            .proof_scope_assumption_infers
                            .store_fact_outputs
                            .iter()
                            .skip(parameter_facts.len()),
                    )
                    .zip(well_definedness.premises.iter())
                    .enumerate()
            {
                let proposition = render_fact(premise, &self.environment_stack)?;
                let premise_name = format!("__domain{}", premise_index + 1);
                binder_declarations.push(format!("({premise_name} : {proposition})"));
                binder_intro_names.push(premise_name.clone());
                self.environment_stack
                    .fact_names
                    .insert(*premise_fact_id, premise_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(*premise_fact_id, premise.clone());

                let premise_well_definedness_fact_id =
                    premise_wd.store.fact_id.ok_or_else(|| {
                        format!("named forall WD premise {premise_index} has no frozen FactId")
                    })?;
                self.environment_stack
                    .fact_names
                    .insert(premise_well_definedness_fact_id, premise_name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(premise_well_definedness_fact_id, premise.clone());

                if premise_output.inferred_facts.len() != premise_output.inferred_fact_ids.len() {
                    return Err(format!(
                        "named forall premise {premise_index} lost an inferred FactId"
                    ));
                }
            }

            self.compile_defined_predicate_inference_results_in_current_environment(
                verification.proof_scope_assumption_infers,
                DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
            )?;
            validate_flattened_inferred_fact_ids_are_visible(
                verification.proof_scope_assumption_infers,
                &self.environment_stack,
                "named forall proof-scope assumptions",
            )?;

            let mut proof_lines = Vec::with_capacity(
                verification.proof_steps.len() + verification.conclusion_checks.len() + 1,
            );
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                proof_lines.extend(lines);
            }

            let mut conclusion_names = Vec::new();
            let mut conclusion_types = Vec::new();
            for (conclusion_index, (conclusion, expected_conclusion)) in verification
                .conclusion_checks
                .iter()
                .zip(verification.forall_fact.then_facts.iter())
                .enumerate()
            {
                let conclusion = conclusion
                    .factual_success()
                    .ok_or_else(|| "named forall conclusion is not factual".to_string())?;
                let expected_conclusion = expected_conclusion.clone().to_fact();
                if conclusion.fact().to_string() != expected_conclusion.to_string()
                    || !conclusion.store.infers.is_empty()
                {
                    return Err(
                        "named forall conclusion changed its target or gained effects".into(),
                    );
                }
                let Some(conclusion_proof) =
                    self.construct_lean_proof_from_direct_fact_result(conclusion)?
                else {
                    return Ok(None);
                };
                let proposition = render_fact(&expected_conclusion, &self.environment_stack)?;
                let conclusion_name =
                    format!("__c{}_{}", self.next_fact_name_index, conclusion_index);
                proof_lines.push(format!(
                    "have {conclusion_name} : {proposition} := {conclusion_proof}"
                ));
                conclusion_names.push(conclusion_name);
                conclusion_types.push(proposition);
            }
            if conclusion_names.len() == 1 {
                proof_lines.push(format!("exact {}", conclusion_names[0]));
            } else {
                proof_lines.push(format!("exact ⟨{}⟩", conclusion_names.join(", ")));
            }
            Ok(Some(CompiledNamedForallStatementProofBody {
                binder_declarations,
                binder_intro_names,
                proof_lines,
                conclusion_type: if conclusion_types.len() == 1 {
                    conclusion_types[0].clone()
                } else {
                    conjunction(
                        &conclusion_types
                            .iter()
                            .map(|conclusion| format!("({conclusion})"))
                            .collect::<Vec<_>>(),
                    )
                },
            }))
        })(
        );
        self.environment_stack.pop_local_environment();
        let Some(body) = compilation? else {
            return Ok(false);
        };

        let theorem_name = lean_identifier(&verification.name);
        let theorem_type = if body.binder_declarations.is_empty() {
            body.conclusion_type
        } else {
            format!(
                "∀ {},\n      {}",
                body.binder_declarations.join(" "),
                body.conclusion_type
            )
        };
        let intro = if body.binder_intro_names.is_empty() {
            String::new()
        } else {
            format!("intro {}\n", body.binder_intro_names.join(" "))
        };
        self.declarations.push(format!(
            "theorem {theorem_name} :\n    {theorem_type} := by\n{}",
            indent_lines(&format!("{intro}{}", body.proof_lines.join("\n")), 2)
        ));
        if let Some(corollary) = native_real_less_to_less_equal_corollary(
            &theorem_name,
            &parameters,
            verification.forall_fact,
            &verification.conclusion_checks,
        ) {
            self.declarations.push(corollary);
        }
        if let Some(theorem_fact_id) = theorem_fact_id {
            self.environment_stack
                .fact_names
                .insert(theorem_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(theorem_fact_id, theorem_fact);
        }
        self.next_fact_name_index += 1;
        Ok(true)
    }

    /// `Combine`: instantiate one previously compiled Litex theorem by its
    /// exact source FactId, combine the ordered argument-membership proofs,
    /// and publish each direct conclusion under the exact store FactId
    /// retained by this statement Result.
    pub(super) fn compile_litex_theorem_instantiation_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<bool, String> {
        let Some(conclusions) =
            self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
        else {
            return Ok(false);
        };
        for conclusion in conclusions {
            let fact_id = conclusion.retained_fact_id.ok_or_else(|| {
                format!(
                    "top-level by-thm conclusion `{}` has no retained FactId",
                    conclusion.fact
                )
            })?;
            let conclusion_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {conclusion_name} : {} := by\n  exact {}",
                conclusion.proposition, conclusion.proof_expression
            ));
            self.environment_stack
                .fact_names
                .insert(fact_id, conclusion_name);
            self.environment_stack
                .fact_propositions
                .insert(fact_id, conclusion.fact);
            self.next_fact_name_index += 1;
        }
        Ok(true)
    }

    /// `Combine`: construct the exact ordered theorem conclusions without
    /// publishing them into the caller's compiler environment. The enclosing
    /// statement decides whether those Result-owned FactIds become visible or
    /// remain local to another proof layer.
    pub(super) fn construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<Option<Vec<CompiledLitexTheoremInstantiationConclusionProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.theorem_source != "litex"
            || verification.mode != "release_all"
            || result.statement.selected_facts.is_some()
            || verification.selected_fact.is_some()
            || !verification.temporary_then_facts.is_empty()
            || !verification.requirement_roles.is_empty()
            || !verification.requirement_checks.is_empty()
            || !verification.domain_facts.is_empty()
            || !verification.domain_checks.is_empty()
        {
            return Ok(None);
        }
        if verification.theorem != result.statement.name.to_string()
            || verification.arguments
                != result
                    .statement
                    .args
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
        {
            return Err("by-thm Result changed its theorem name or argument order".into());
        }
        let source_fact_id = verification
            .source_fact_id
            .ok_or_else(|| "by-thm Result has no source theorem FactId".to_string())?;
        let source_fact = self
            .environment_stack
            .fact_propositions
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| format!("by-thm cited unavailable source FactId `{source_fact_id}`"))?;
        let Fact::ForallFact(source_forall) = &source_fact else {
            return Err("by-thm source FactId does not identify a forall fact".into());
        };
        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if !source_forall.dom_facts.is_empty()
            || source_parameters.iter().any(|(_, parameter_type)| {
                !matches!(parameter_type, ParamType::Obj(Obj::StandardSet(_)))
            })
        {
            return Ok(None);
        }
        if source_parameters.len() != result.statement.args.len()
            || source_forall.then_facts.len() != verification.direct_conclusions.len()
            || verification.direct_conclusions.is_empty()
        {
            return Err("by-thm Result changed its source theorem arity".into());
        }
        let Some(argument_verification) = &verification.argument_verification else {
            return Err("by-thm Result has no argument verification children".into());
        };
        if !argument_verification.infers.is_empty()
            || argument_verification.checks.len() != source_parameters.len()
        {
            return Ok(None);
        }

        let direct_conclusion_strings = verification
            .direct_conclusions
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>();
        if verification.stored_then_facts != direct_conclusion_strings
            || verification.parent_stored_facts != direct_conclusion_strings
        {
            return Err("by-thm Result changed its direct conclusion order".into());
        }
        if result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
            || !result.common.infers.rule_applications.is_empty()
        {
            return Ok(None);
        }
        if result.common.infers.store_fact_outputs.len() != verification.direct_conclusions.len() {
            return Err("by-thm Result changed its direct conclusion store count".into());
        }
        let conclusion_fact_ids = result
            .common
            .infers
            .store_fact_outputs
            .iter()
            .zip(verification.direct_conclusions.iter())
            .map(|(stored, expected)| {
                if stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                    return Err(
                        "by-thm Result changed a direct conclusion store proposition".into(),
                    );
                }
                Ok(stored.fact_id)
            })
            .collect::<Result<Vec<_>, String>>()?;

        let theorem_name = self
            .environment_stack
            .fact_names
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| format!("by-thm source FactId `{source_fact_id}` has no Lean name"))?;
        let mut application_parts = vec![theorem_name];
        for (parameter_index, (((_, parameter_type), argument), check)) in source_parameters
            .iter()
            .zip(result.statement.args.iter())
            .zip(argument_verification.checks.iter())
            .enumerate()
        {
            let parameter_set = parameter_set(parameter_type)
                .map_err(|error| format!("by-thm parameter {parameter_index}: {error}"))?;
            let rendered_argument = render_obj(argument, &self.environment_stack)?;
            let expected_parameter_fact = format!(
                "Litex.In {rendered_argument} {}",
                render_obj(parameter_set, &self.environment_stack)?
            );
            let factual_check = check
                .factual_success()
                .ok_or_else(|| format!("by-thm argument check {parameter_index} is not factual"))?;
            if render_fact(&factual_check.fact(), &self.environment_stack)?
                != expected_parameter_fact
                || !factual_check.store.infers.is_empty()
            {
                return Err(format!(
                    "by-thm argument check {parameter_index} changed its parameter obligation"
                ));
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            application_parts.push(rendered_argument);
            application_parts.push(format!("({parameter_proof})"));
        }
        let theorem_application = format!("({})", application_parts.join(" "));

        let mut conclusions = Vec::with_capacity(verification.direct_conclusions.len());
        for (conclusion_index, (conclusion, fact_id)) in verification
            .direct_conclusions
            .iter()
            .zip(conclusion_fact_ids.iter())
            .enumerate()
        {
            let proof = conjunction_projection(
                &theorem_application,
                conclusion_index,
                verification.direct_conclusions.len(),
            )?;
            let proposition = render_fact(conclusion, &self.environment_stack)?;
            conclusions.push(CompiledLitexTheoremInstantiationConclusionProofBody {
                retained_fact_id: *fact_id,
                fact: conclusion.clone(),
                proposition,
                proof_expression: proof,
            });
        }
        Ok(Some(conclusions))
    }

    pub(super) fn compile_ordinary_fact_goal_proof_body(
        &mut self,
        source_fact: &Fact,
        source_proof_step_count: usize,
        verification: &SuccessVerifyClaimFactResult,
    ) -> Result<Option<CompiledOrdinaryFactGoalProofBody>, String> {
        if verification.fact.to_string() != source_fact.to_string()
            || verification.proof_steps.len() != source_proof_step_count
        {
            return Err("ordinary fact goal Result changed its target or proof-step order".into());
        }
        if !verification.proof_scope.assumption_infers.is_empty()
            || !verification.proof_scope.assumption_components.is_empty()
        {
            return Err("ordinary fact goal retained unexpected local assumptions".into());
        }
        if matches!(source_fact, Fact::AtomicFact(_)) {
            validate_atomic_fact_well_definedness_result(
                &verification.well_definedness,
                source_fact,
            )?;
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let mut local_proof_lines = Vec::with_capacity(verification.proof_steps.len());
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Ok(None);
                };
                local_proof_lines.extend(lines);
            }

            let conclusion = verification
                .conclusion_check
                .factual_success()
                .ok_or_else(|| "ordinary fact goal conclusion is not factual".to_string())?;
            if conclusion.fact().to_string() != source_fact.to_string()
                || !conclusion.store.infers.is_empty()
            {
                return Err(
                    "ordinary fact goal conclusion changed its target or gained effects".into(),
                );
            }
            let Some(conclusion_proof) =
                self.construct_lean_proof_from_direct_fact_result(conclusion)?
            else {
                return Ok(None);
            };
            let proposition = render_fact(source_fact, &self.environment_stack)?;
            Ok(Some(CompiledOrdinaryFactGoalProofBody {
                local_proof_lines,
                proposition,
                conclusion_proof,
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    pub(super) fn compile_stmt_result_as_local_proof_steps(
        &mut self,
        result: &StmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
        if let StmtResult::Success(SuccessStmtResult::Definition(
            SuccessDefinitionStmtResult::LetObjStmt(result),
        )) = result
        {
            return self.compile_let_obj_stmt_result_as_local_proof_steps(result, proof_step_index);
        }
        if let Some(factual) = result.factual_success() {
            return self
                .compile_fact_stmt_result_as_local_proof_step(factual, proof_step_index)
                .map(|line| line.map(|line| vec![line]));
        }
        if let StmtResult::Success(SuccessStmtResult::By(by_result)) = result {
            if let SuccessByStmtResult::ByDefStmt(result) = by_result {
                return self.compile_by_definition_stmt_result_as_local_proof_steps(
                    result,
                    proof_step_index,
                );
            }
            if let SuccessByStmtResult::ByEnumerateFiniteSetStmt(result) = by_result {
                let Some(proof) =
                    self.construct_lean_proof_from_by_enumerate_finite_set_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local by-enumerate generated forall",
                )?;
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, proof.fact);
                return Ok(Some(vec![format!(
                    "have {name} : {} := {}",
                    proof.proposition, proof.proof_expression
                )]));
            }
            if let SuccessByStmtResult::ByForStmt(result) = by_result {
                let Some(proof) = self.construct_lean_proof_from_by_for_stmt_result(result)? else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local by-for generated forall",
                )?;
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, proof.fact);
                return Ok(Some(vec![format!(
                    "have {name} : {} := {}",
                    proof.proposition, proof.proof_expression
                )]));
            }
            let (proofs, effects) = match by_result {
                SuccessByStmtResult::ByCasesStmt(result) => (
                    self.construct_lean_proofs_from_by_cases_stmt_result(result)?,
                    &result.common.infers,
                ),
                SuccessByStmtResult::ByContraStmt(result) => (
                    self.construct_lean_proof_from_by_contra_stmt_result(result)?
                        .map(|proof| vec![proof]),
                    &result.common.infers,
                ),
                SuccessByStmtResult::ByExtensionStmt(result) => (
                    self.construct_lean_proof_from_by_extension_stmt_result(result)?
                        .map(|proof| vec![proof]),
                    &result.common.infers,
                ),
                _ => return Ok(None),
            };
            let Some(proofs) = proofs else {
                return Ok(None);
            };
            let fact_ids = validate_compiled_fact_proof_effects(
                effects,
                &proofs,
                &self.environment_stack,
                "local by-statement outputs",
            )?;
            let multiple_outputs = proofs.len() > 1;
            let mut lines = Vec::with_capacity(proofs.len());
            for (output_index, (proof, fact_id)) in proofs.into_iter().zip(fact_ids).enumerate() {
                let name = if multiple_outputs {
                    format!("__step{proof_step_index}_{}", output_index + 1)
                } else {
                    format!("__step{proof_step_index}")
                };
                if let Some(fact_id) = fact_id {
                    self.environment_stack
                        .fact_names
                        .insert(fact_id, name.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(fact_id, proof.fact);
                }
                lines.push(format!(
                    "have {name} : {} := by\n  exact {}",
                    proof.proposition, proof.proof_expression
                ));
            }
            return Ok(Some(lines));
        }
        let StmtResult::Success(SuccessStmtResult::Witness(
            SuccessWitnessStmtResult::WitnessExistFact(result),
        )) = result
        else {
            return Ok(None);
        };
        let Some(proof_body) =
            self.construct_lean_proof_from_witness_exist_fact_stmt_result(result)?
        else {
            return Ok(None);
        };
        let existential: Fact = result.statement.exist_fact_in_witness.clone().into();
        let fact_id = validate_single_fact_store_output(
            &result.common.infers,
            &existential,
            "local existential witness effect",
        )?;
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, existential);
        Ok(Some(vec![format!(
            "have {name} : {} := by\n  exact {}",
            proof_body.proposition, proof_body.proof_expression
        )]))
    }

    /// `Combine`: a local `let` publishes its symbol and exact defining
    /// equality only in the compiler frame that owns the surrounding proof.
    /// The recursive proof-step consumer therefore needs no separate
    /// local-environment IR and no Runtime lookup.
    pub(super) fn compile_let_obj_stmt_result_as_local_proof_steps(
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
    pub(super) fn compile_by_definition_stmt_result_as_local_proof_steps(
        &mut self,
        result: &SuccessByDefStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<Vec<String>>, String> {
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
        let lines = vec![format!(
            "have {target_name} : {} := by\n  exact {}",
            proof.target.proposition, proof.target.proof_expression
        )];
        self.environment_stack
            .fact_names
            .insert(target_fact_id, target_name);
        self.environment_stack
            .fact_propositions
            .insert(target_fact_id, proof.target.fact.clone());
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "local by-definition Result",
        )?;
        Ok(Some(lines))
    }

    pub(super) fn compile_fact_stmt_result_as_local_proof_step(
        &mut self,
        result: &SuccessFactStmtResult,
        proof_step_index: usize,
    ) -> Result<Option<String>, String> {
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
            if !result.store.infers.rule_applications.is_empty()
                || result.store.infers.store_fact_outputs.len() != 1
            {
                return Ok(None);
            }
            let stored = &result.store.infers.store_fact_outputs[0];
            if stored.fact_id != Some(fact_id)
                || stored.itself_and_why_itself_is_stored.0.to_string() != source_fact.to_string()
                || !stored.inferred_facts.is_empty()
                || !stored.inferred_fact_ids.is_empty()
            {
                return Err("local proof-step store does not retain its exact FactId".into());
            }
        }
        let Some(proof) = self.construct_lean_proof_from_direct_fact_result(result)? else {
            return Ok(None);
        };
        let proposition = render_fact(&source_fact, &self.environment_stack)?;
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact);
        Ok(Some(format!(
            "have {name} : {proposition} := by\n  exact {proof}"
        )))
    }
}

/// Expose the first reviewed Mathlib-native theorem view. The source shape is
/// deliberately closed: two direct `R` binders, their strict-order premise,
/// and the matching non-strict conclusion proved by allowlisted typed
/// strict-to-weak order evidence. Canonical and native views are sibling
/// replays of that one Result: this route never assumes that `In.rep`, which
/// uses classical choice, is definitionally the native input. Unsupported
/// wrappers or proof evidence keep only the canonical view.
fn native_real_less_to_less_equal_corollary(
    canonical_theorem_name: &str,
    parameters: &[(SymbolBinding, ParamType)],
    forall_fact: &ForallFact,
    conclusion_checks: &[&StmtResult],
) -> Option<String> {
    let [(left_binding, left_type), (right_binding, right_type)] = parameters else {
        return None;
    };
    if !matches!(left_type, ParamType::Obj(Obj::StandardSet(StandardSet::R)))
        || !matches!(right_type, ParamType::Obj(Obj::StandardSet(StandardSet::R)))
    {
        return None;
    }
    let [premise] = forall_fact.dom_facts.as_slice() else {
        return None;
    };
    let Fact::AtomicFact(AtomicFact::LessFact(premise)) = premise else {
        return None;
    };
    let [conclusion] = forall_fact.then_facts.as_slice() else {
        return None;
    };
    let conclusion = conclusion.clone().to_fact();
    let Fact::AtomicFact(AtomicFact::LessEqualFact(conclusion)) = &conclusion else {
        return None;
    };
    if !object_is_exact_symbol(&premise.left, left_binding)
        || !object_is_exact_symbol(&premise.right, right_binding)
        || !object_is_exact_symbol(&conclusion.left, left_binding)
        || !object_is_exact_symbol(&conclusion.right, right_binding)
    {
        return None;
    }
    let [conclusion_check] = conclusion_checks else {
        return None;
    };
    let conclusion_success = conclusion_check.factual_success()?;
    let builtin = match conclusion_success.proof() {
        SuccessFactProofResult::BuiltinRule(builtin)
        | SuccessFactProofResult::BuiltinStrategy(builtin) => builtin,
        _ => return None,
    };
    let replays_strict_to_weak_order = match builtin.evidence.typed() {
        Some(BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::LessEqualFromStrictOrder)) => {
            true
        }
        Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) => {
            evidence.rule_id.as_str() == LESS_EQUAL_OF_LESS_RULE_ID
                && evidence.semantic_fingerprint.as_hex() == LESS_EQUAL_OF_LESS_FINGERPRINT
        }
        _ => false,
    };
    if !replays_strict_to_weak_order {
        return None;
    }

    let left_name = lean_identifier(left_binding.name());
    let right_name = lean_identifier(right_binding.name());
    let proof = format!(
        "exact Litex.OrderBridge.real_le_iff.mp\n  \
         (Litex.Lt.toLe (Litex.OrderBridge.ltOfReal __domain1))"
    );
    Some(format!(
        "namespace Native\n\n\
         theorem {canonical_theorem_name} ({left_name} {right_name} : ℝ) \
         (__domain1 : {left_name} < {right_name}) : {left_name} ≤ {right_name} := by\n{}\n\n\
         end Native",
        indent_lines(&proof, 2)
    ))
}

fn object_is_exact_symbol(object: &Obj, binding: &SymbolBinding) -> bool {
    matches!(
        LeanTargetObjectRepresentation::lower(object),
        Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. })
            if symbol_id == binding.id()
    )
}
