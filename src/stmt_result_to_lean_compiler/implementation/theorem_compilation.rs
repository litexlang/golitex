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
            if !matches!(
                type_check_proof.evidence.typed(),
                Some(BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyNonEquationalAtomicFactWithBuiltinRulesInner
                ))
            ) || !type_check_proof.subgoals.is_empty()
                || factual_type_check.fact_id.is_some()
                || !factual_type_check.infers.is_empty()
            {
                return Err(
                    "Template set-alias body type check changed its typed rule, children, or stores"
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

        let proof_scope_has_defined_predicate_inference = verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| defined_predicate_infer_rule(&application.rule));
        let proof_scope_has_direct_inference = verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            });
        if proof_scope_has_defined_predicate_inference && proof_scope_has_direct_inference {
            return Ok(false);
        }
        if verification
            .proof_scope_assumption_infers
            .rule_applications
            .iter()
            .any(|application| {
                !defined_predicate_infer_rule(&application.rule)
                    && !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
            })
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

        let theorem_well_definedness = self
            .construct_well_definedness_to_lean_compilation_context(
                verification.well_definedness,
            )?;
        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(theorem_well_definedness.clone());
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
                if matches!(parameter_set, Obj::StandardSet(StandardSet::Z)) {
                    validate_object_parameter_premise(binding.id(), parameter_set, parameter)?;
                    binder_declarations.push(format!("({parameter_name} : ℤ)"));
                    binder_intro_names.push(parameter_name.clone());
                    let parameter_proof = format!("(Litex.In.own Litex.Z {parameter_name})");
                    self.environment_stack
                        .fact_names
                        .insert(*fact_id, parameter_proof.clone());
                    self.environment_stack
                        .fact_propositions
                        .insert(*fact_id, parameter.clone());
                    install_parameter_fact_aliases(
                        binding.id(),
                        parameter,
                        &parameter_proof,
                        parameter_set,
                        &mut self.environment_stack,
                    )?;
                    install_structured_induction_native_integer_symbol(
                        binding.id(),
                        &parameter_name,
                        &mut self.environment_stack,
                    );
                    continue;
                }
                let (_, retained_parameter_set) = membership_parts(parameter)?;
                let rendered_parameter_set =
                    render_obj(retained_parameter_set, &self.environment_stack)?;
                let carrier_name = format!(
                    "__carrier{}_{}",
                    self.next_fact_name_index,
                    parameter_index + 1
                );
                match parameter_set {
                    Obj::FnSet(_) | Obj::FiniteSeqSet(_) | Obj::SeqSet(_) => {
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

            if proof_scope_has_defined_predicate_inference {
                self.compile_defined_predicate_inference_results_in_current_environment(
                    verification.proof_scope_assumption_infers,
                    DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
                )?;
            } else if proof_scope_has_direct_inference {
                let allowed_sources = assumption_fact_ids
                    .iter()
                    .copied()
                    .zip(assumption_facts.iter().cloned())
                    .collect::<Vec<_>>();
                self.compile_typed_inference_results_in_current_compiler_environment(
                    verification.proof_scope_assumption_infers,
                    &allowed_sources,
                    CompiledInferenceFactAvailabilityInLeanEnvironment::InlineProofExpression,
                    "named forall proof-scope assumptions",
                    None,
                )?;
            }
            validate_flattened_inferred_fact_ids_are_visible(
                verification.proof_scope_assumption_infers,
                &self.environment_stack,
                "named forall proof-scope assumptions",
            )?;

            // Runtime completes theorem well-definedness before executing any
            // proof step, so every intrinsic store produced by the named
            // premise/conclusion WD children is already visible here.
            for premise in &well_definedness.premises {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    premise.well_definedness.as_ref(),
                    &mut self.environment_stack,
                )?;
            }
            for conclusion in &well_definedness.conclusions {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    conclusion.well_definedness.as_ref(),
                    &mut self.environment_stack,
                )?;
            }

            let mut proof_lines = Vec::with_capacity(
                verification.proof_steps.len() + verification.conclusion_checks.len() + 1,
            );
            for (proof_step_index, proof_step) in verification.proof_steps.iter().enumerate() {
                let Some(lines) = self
                    .compile_stmt_result_as_local_proof_steps(proof_step, proof_step_index + 1)?
                else {
                    return Err(format!(
                        "named forall proof step {} has no local compiler consumer",
                        proof_step_index + 1
                    ));
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
                    return Err(format!(
                        "named forall conclusion {} has no direct proof consumer",
                        conclusion_index + 1
                    ));
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
        if let Some(theorem_fact_id) = theorem_fact_id {
            self.environment_stack
                .fact_names
                .insert(theorem_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(theorem_fact_id, theorem_fact);
            self.environment_stack
                .fact_well_definedness
                .insert(theorem_fact_id, theorem_well_definedness);
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
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let Some(conclusions) =
            self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
        else {
            return Ok(false);
        };
        for conclusion in conclusions {
            let fact_id = conclusion.retained_fact_id.ok_or_else(|| {
                format!(
                    "top-level release-thm conclusion `{}` has no retained FactId",
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

    /// Compile a reserved builtin theorem only from its typed identity and
    /// retained requirement child.  Most builtin theorem interfaces are an
    /// explicit name for a proof route that already returned the exact
    /// conclusion as a factual child Result; replay that child directly rather
    /// than rediscovering the fact from its spelling.
    pub(super) fn compile_builtin_theorem_application_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let Some(verification) = &result.verification else {
            return Ok(false);
        };
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &verification.source
        else {
            return Ok(false);
        };
        if matches!(
            source.theorem_id,
            BuiltinTheoremId::RealLeastUpperBoundExists
                | BuiltinTheoremId::RealMemberLeLeastUpperBound
                | BuiltinTheoremId::RealLeastUpperBoundLeUpperBound
                | BuiltinTheoremId::RationalBetweenReals
        ) {
            return self.compile_real_analysis_builtin_theorem_application(result);
        }
        if source.conclusion_well_definedness.is_some() {
            return Err(
                "ordinary builtin theorem unexpectedly retained dedicated conclusion WD evidence"
                    .into(),
            );
        }
        if verification.theorem != source.theorem_id.as_str()
            || verification.theorem != result.statement.name.to_string()
            || verification.arguments.len() != result.statement.args.len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args.iter())
                .any(|(retained, source)| obj_equality_key(retained) != obj_equality_key(source))
        {
            return Err("builtin theorem Result changed its identity or argument order".into());
        }
        let expected_roles = builtin_theorem_requirement_roles(source.theorem_id);
        if source.requirement_roles != expected_roles
            || source.requirement_facts.len() != source.requirement_roles.len()
            || source.requirement_checks.len() != source.requirement_roles.len()
        {
            return Err("builtin theorem Result changed its typed requirement schema".into());
        }
        let expected_provenance = match source.theorem_id {
            BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromFamily
            | BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromPointwise => {
                Some(BuiltinTheoremProvenance::AxiomOfChoice)
            }
            _ => None,
        };
        if source.provenance != expected_provenance {
            return Err("builtin theorem Result changed its typed provenance".into());
        }
        let [conclusion] = verification.direct_conclusions.as_slice() else {
            return Err("builtin theorem Result must retain exactly one direct conclusion".into());
        };

        // These three interfaces need dedicated target theorems rather than a
        // conclusion-shaped child.  They remain fail-closed until those exact
        // ABI lemmas are installed below this shared typed entry point.
        if let Some(limitation) = match source.theorem_id {
            BuiltinTheoremId::SubsetOfFiniteSetIsFinite => Some(
                "builtin theorem `subset_of_finite_set_is_finite` requires an exact finite-subcarrier transport theorem for Litex.Set",
            ),
            BuiltinTheoremId::FiniteSetHasBijectiveIndex => Some(
                "builtin theorem `finite_set_has_bijective_index` requires an exact finite-carrier enumeration and bijection target ABI",
            ),
            BuiltinTheoremId::RationalHasUniqueReducedFraction => Some(
                "builtin theorem `rational_has_unique_reduced_fraction` requires a reviewed bridge from heterogeneous Litex.Same to the native rational normal form",
            ),
            BuiltinTheoremId::RealGreatestLowerBoundExists
            | BuiltinTheoremId::RealGreatestLowerBoundLeMember
            | BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound => Some(
                "real greatest-lower-bound builtin theorems are currently Litex-kernel-only; the Lean rule adapter has not been installed",
            ),
            _ => None,
        } {
            return Err(limitation.into());
        }

        let [requirement_fact] = source.requirement_facts.as_slice() else {
            return Err(
                "builtin theorem direct adapter requires one retained requirement fact".into(),
            );
        };
        let [requirement_check] = source.requirement_checks.as_slice() else {
            return Err(
                "builtin theorem direct adapter requires one retained requirement child".into(),
            );
        };
        if requirement_fact.to_string() != conclusion.to_string() {
            return Err("builtin theorem direct adapter requirement changed its conclusion".into());
        }
        let requirement_check = requirement_check
            .factual_success()
            .ok_or_else(|| "builtin theorem requirement child is not factual".to_string())?;
        validate_scoped_fact_check_result(
            requirement_check,
            conclusion,
            "builtin theorem requirement child",
        )?;
        let [outer_store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err("builtin theorem must retain exactly one outer conclusion store".into());
        };
        let checked_fact_id = requirement_check
            .store
            .fact_id
            .ok_or_else(|| "builtin theorem checked conclusion has no frozen FactId".to_string())?;
        if outer_store.itself_and_why_itself_is_stored.0.to_string() != conclusion.to_string()
            || outer_store.fact_id != Some(checked_fact_id)
            || outer_store.inferred_facts.len() != outer_store.inferred_fact_ids.len()
        {
            return Err(
                "builtin theorem outer publication changed the checked conclusion's root fact, FactId, or inferred child arity"
                    .into(),
            );
        }
        self.install_atomic_fact_well_definedness_store_results(requirement_check)
            .map_err(|error| {
                format!(
                    "builtin theorem `{}` checked-conclusion WD installation: {error}",
                    source.theorem_id
                )
            })?;
        let Some(proof) = self
            .construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
                requirement_check,
            )?
        else {
            return Err(format!(
                "builtin theorem `{}` checked conclusion has no direct typed proof consumer",
                source.theorem_id
            ));
        };
        let proposition = if requirement_check.well_definedness.recursive.is_some() {
            self.render_fact_using_well_definedness_result(
                &requirement_check.well_definedness,
                conclusion,
            )?
        } else {
            render_fact(conclusion, &self.environment_stack)?
        };
        let source_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {source_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(checked_fact_id, source_name.clone());
        self.environment_stack
            .fact_propositions
            .insert(checked_fact_id, conclusion.clone());
        self.next_fact_name_index += 1;

        if result.common.infers.rule_applications.is_empty()
            && outer_store.inferred_facts.is_empty()
            && outer_store.inferred_fact_ids.is_empty()
        {
            return Ok(true);
        }
        if source.theorem_id == BuiltinTheoremId::SetBuilderMember {
            self.compile_set_builder_membership_infer_result_as_top_level_declarations(
                conclusion,
                checked_fact_id,
                &source_name,
                &result.common.infers,
            )?;
        } else if source.theorem_id == BuiltinTheoremId::CartesianMemberFromCoordinates {
            self.compile_literal_cartesian_membership_infer_result_as_top_level_declarations(
                requirement_check,
                conclusion,
                checked_fact_id,
                &result.common.infers,
            )?;
        } else {
            self.compile_typed_infer_result_as_top_level_declarations_with_allowed_sources(
                &result.common.infers,
                &[(checked_fact_id, conclusion.clone())],
                &format!("builtin theorem `{}` outer inference", source.theorem_id),
            )?;
        }
        Ok(true)
    }

    fn compile_real_analysis_builtin_theorem_application(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<bool, String> {
        let verification = result
            .verification
            .as_ref()
            .ok_or_else(|| "real-analysis builtin theorem lost its verification".to_string())?;
        let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) = &verification.source
        else {
            return Err("real-analysis builtin theorem lost its typed source".into());
        };
        if verification.theorem != source.theorem_id.as_str()
            || verification.theorem != result.statement.name.to_string()
            || verification.arguments.len() != result.statement.args.len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args.iter())
                .any(|(retained, statement)| !same_compiler_object(retained, statement))
        {
            return Err(
                "real-analysis builtin theorem Result changed its identity or argument order"
                    .into(),
            );
        }
        let expected_roles = builtin_theorem_requirement_roles(source.theorem_id);
        if source.requirement_roles != expected_roles
            || source.requirement_facts.len() != expected_roles.len()
            || source.requirement_checks.len() != expected_roles.len()
            || source.provenance.is_some()
        {
            return Err(
                "real-analysis builtin theorem Result changed its typed requirement schema".into(),
            );
        }
        let conclusion_well_definedness =
            source.conclusion_well_definedness.as_ref().ok_or_else(|| {
                "real-analysis builtin theorem lost dedicated conclusion WD evidence".to_string()
            })?;
        let [conclusion] = verification.direct_conclusions.as_slice() else {
            return Err("real-analysis builtin theorem must retain one direct conclusion".into());
        };
        validate_real_analysis_builtin_contract(
            source.theorem_id,
            &verification.arguments,
            &source.requirement_facts,
            conclusion,
        )?;

        let mut requirement_proofs = Vec::with_capacity(source.requirement_checks.len());
        for (index, (requirement, check)) in source
            .requirement_facts
            .iter()
            .zip(source.requirement_checks.iter())
            .enumerate()
        {
            let check = check.factual_success().ok_or_else(|| {
                format!(
                    "real-analysis builtin requirement {} is not factual",
                    index + 1
                )
            })?;
            validate_scoped_fact_check_result(
                check,
                requirement,
                "real-analysis builtin requirement child",
            )?;
            self.install_atomic_fact_well_definedness_store_results(check)
                .map_err(|error| {
                    format!(
                        "real-analysis builtin requirement {} WD installation: {error}",
                        index + 1
                    )
                })?;
            let proof = if matches!(check.proof(), SuccessFactProofResult::ForallProof(_)) {
                let theorem_name = format!("__fact{}", self.next_fact_name_index);
                let declaration_count = self.declarations.len();
                let fact_index = self.next_fact_name_index;
                if !self.compile_direct_forall_fact_result(check)? {
                    return Err(format!(
                        "real-analysis builtin requirement {} retained an unsupported ForallProof",
                        index + 1
                    ));
                }
                if self.declarations.len() != declaration_count + 1
                    || self.next_fact_name_index != fact_index + 1
                {
                    return Err(format!(
                        "real-analysis builtin requirement {} compiled an unexpected number of forall projections",
                        index + 1
                    ));
                }
                theorem_name
            } else {
                self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(check)?
                    .ok_or_else(|| {
                        format!(
                        "real-analysis builtin requirement {} has no direct typed proof consumer",
                        index + 1
                    )
                    })?
            };
            requirement_proofs.push(format!("({proof})"));
        }

        let rendered_arguments = verification
            .arguments
            .iter()
            .map(|argument| render_obj(argument, &self.environment_stack))
            .collect::<Result<Vec<_>, _>>()?;
        let rule_name = match source.theorem_id {
            BuiltinTheoremId::RealLeastUpperBoundExists => "Litex.Rules.realLeastUpperBoundExists",
            BuiltinTheoremId::RealMemberLeLeastUpperBound => {
                "Litex.Rules.realMemberLeLeastUpperBound"
            }
            BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => {
                "Litex.Rules.realLeastUpperBoundLeUpperBound"
            }
            BuiltinTheoremId::RationalBetweenReals => "Litex.Rules.rationalBetweenReals",
            _ => unreachable!("typed real-analysis theorem set was checked above"),
        };
        let proof = format!(
            "{rule_name} {} {}",
            rendered_arguments.join(" "),
            requirement_proofs.join(" ")
        );
        let proposition = self
            .render_fact_using_well_definedness_result(conclusion_well_definedness, conclusion)?;

        let [outer_store] = result.common.infers.store_fact_outputs.as_slice() else {
            return Err(
                "real-analysis builtin theorem must retain one outer conclusion store".into(),
            );
        };
        let conclusion_fact_id = outer_store.fact_id.ok_or_else(|| {
            "real-analysis builtin theorem conclusion has no frozen FactId".to_string()
        })?;
        if outer_store.itself_and_why_itself_is_stored.0.to_string() != conclusion.to_string()
            || !outer_store.inferred_facts.is_empty()
            || !outer_store.inferred_fact_ids.is_empty()
            || !result.common.infers.rule_applications.is_empty()
        {
            return Err("real-analysis builtin theorem changed its publication effects".into());
        }
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
        ));
        self.environment_stack
            .fact_names
            .insert(conclusion_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(conclusion_fact_id, conclusion.clone());
        self.next_fact_name_index += 1;
        Ok(true)
    }

    fn compile_literal_cartesian_membership_infer_result_as_top_level_declarations(
        &mut self,
        requirement_check: &SuccessFactStmtResult,
        source_fact: &Fact,
        source_fact_id: FactId,
        infers: &SuccessInferResult,
    ) -> Result<(), String> {
        let SuccessFactProofResult::BuiltinRule(builtin) = requirement_check.proof() else {
            return Err("literal cart membership lost its builtin proof Result".into());
        };
        let Some(BuiltinRuleEvidence::TupleCartesianMembership(evidence)) =
            builtin.evidence.typed()
        else {
            return Err("literal cart membership lost its typed coordinate evidence".into());
        };
        let Some(coordinate_proofs) = self
            .construct_lean_tuple_cartesian_coordinate_proofs_from_result(
                evidence,
                &builtin.subgoals,
            )?
        else {
            return Err("literal cart membership coordinate proof has no direct consumer".into());
        };
        let Fact::AtomicFact(AtomicFact::InFact(source_membership)) = source_fact else {
            return Err("literal cart inference source is not membership".into());
        };
        let (Obj::Tuple(tuple), Obj::Cart(cart)) =
            (&source_membership.element, &source_membership.set)
        else {
            return Err("literal cart inference source retained nonliteral operands".into());
        };
        let coordinate_count = tuple.args.len();
        if coordinate_count != cart.args.len()
            || coordinate_count != coordinate_proofs.len()
            || infers.rule_applications.len() != coordinate_count + 2
        {
            return Err("literal cart inference changed its projection arity".into());
        }

        for (application_index, application) in infers.rule_applications.iter().enumerate() {
            let [premise] = application.premises.as_slice() else {
                return Err(format!(
                    "literal cart projection {application_index} must cite one premise"
                ));
            };
            if premise.fact_id != Some(source_fact_id)
                || premise.fact.to_string() != source_fact.to_string()
            {
                return Err(format!(
                    "literal cart projection {application_index} changed its source FactId"
                ));
            }
            let [conclusion] = application.conclusions.as_slice() else {
                return Err(format!(
                    "literal cart projection {application_index} must retain one conclusion"
                ));
            };
            let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
                format!("literal cart projection {application_index} has no FactId")
            })?;
            let (expected_fact, expected_projection, proof) = if application_index == 0 {
                let rendered_tuple =
                    render_obj(&source_membership.element, &self.environment_stack)?;
                (
                    Fact::from(IsTupleFact::new(
                        source_membership.element.clone(),
                        default_line_file(),
                    )),
                    CartesianMembershipProjectionKind::TupleShape,
                    format!("Litex.tupleShape_isTuple {rendered_tuple}"),
                )
            } else if application_index == 1 {
                (
                    Fact::from(EqualFact::new(
                        TupleDim::new(source_membership.element.clone()).into(),
                        Number::new(coordinate_count.to_string()).into(),
                        default_line_file(),
                    )),
                    CartesianMembershipProjectionKind::TupleDimension,
                    "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                        .to_string(),
                )
            } else {
                let coordinate_index = application_index - 2;
                (
                    evidence.expected_coordinate_memberships[coordinate_index].clone(),
                    CartesianMembershipProjectionKind::Coordinate {
                        index: coordinate_index,
                    },
                    coordinate_proofs[coordinate_index].clone(),
                )
            };
            let InferRule::CartesianMembershipProjection(rule) = &application.rule else {
                return Err(format!(
                    "literal cart projection {application_index} lost its typed rule"
                ));
            };
            if rule.coordinate_count != coordinate_count
                || rule.projection != expected_projection
                || conclusion.fact.to_string() != expected_fact.to_string()
            {
                return Err(format!(
                    "literal cart projection {application_index} changed its typed target"
                ));
            }

            if self
                .environment_stack
                .fact_propositions
                .contains_key(&conclusion_fact_id)
            {
                resolve_fact_citation(
                    &conclusion_fact_id,
                    &conclusion.fact,
                    &self.environment_stack,
                )?;
                continue;
            }
            if !infer_result_retains_fact_id(infers, &conclusion.fact, conclusion_fact_id) {
                return Err(format!(
                    "literal cart projection {application_index} is absent from its flattened store effects"
                ));
            }
            let proposition = render_fact(&conclusion.fact, &self.environment_stack)?;
            let theorem_name = format!("__fact{}", self.next_fact_name_index);
            self.declarations.push(format!(
                "theorem {theorem_name} : {proposition} := by\n  exact {proof}"
            ));
            self.environment_stack
                .fact_names
                .insert(conclusion_fact_id, theorem_name);
            self.environment_stack
                .fact_propositions
                .insert(conclusion_fact_id, conclusion.fact.clone());
            self.next_fact_name_index += 1;
        }
        validate_flattened_inferred_fact_ids_are_visible(
            infers,
            &self.environment_stack,
            "literal cart membership inference",
        )
    }

    /// `Combine`: replay one theorem application in a child compiler scope,
    /// prove the selected atomic consequence from those exact temporary
    /// FactIds, and publish only the parent store owned by `by thm`.
    pub(super) fn compile_by_theorem_selection_stmt_result_to_lean_source(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<bool, String> {
        let Some(body) = self.construct_lean_proof_from_by_theorem_selection_stmt_result(result)?
        else {
            return Ok(false);
        };
        let theorem_name = format!("__fact{}", self.next_fact_name_index);
        self.declarations.push(format!(
            "theorem {theorem_name} : {} := by\n{}",
            body.proposition,
            indent_lines(&body.proof_lines.join("\n"), 2)
        ));
        self.environment_stack
            .fact_names
            .insert(body.retained_fact_id, theorem_name);
        self.environment_stack
            .fact_propositions
            .insert(body.retained_fact_id, body.fact);
        self.next_fact_name_index += 1;
        self.compile_defined_predicate_inference_results_in_current_environment(
            &result.common.infers,
            DefinedPredicateInferenceConclusionPublication::PersistentLeanTheorem,
        )?;
        validate_flattened_inferred_fact_ids_are_visible(
            &result.common.infers,
            &self.environment_stack,
            "by-thm selected parent fact",
        )?;
        Ok(true)
    }

    fn construct_lean_proof_from_by_theorem_selection_stmt_result(
        &mut self,
        result: &SuccessByThmStmtResult,
    ) -> Result<Option<CompiledByTheoremSelectionProofBody>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        if verification.selected_fact.to_string() != result.statement.selected_fact.to_string() {
            return Err("by-thm Result changed its selected fact".into());
        }
        let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(application)) =
            verification.temporary_application.as_ref()
        else {
            return Err("by-thm Result did not retain a temporary release-thm statement".into());
        };
        if application.statement.name.to_string() != result.statement.name.to_string()
            || application.statement.args.len() != result.statement.args.len()
            || application
                .statement
                .args
                .iter()
                .zip(result.statement.args.iter())
                .any(|(actual, expected)| obj_equality_key(actual) != obj_equality_key(expected))
        {
            return Err("by-thm temporary application changed its theorem or arguments".into());
        }

        self.environment_stack.push_inherited_environment();
        let compilation = (|| {
            let Some(mut proof_lines) = self
                .compile_stmt_result_as_local_proof_steps(&verification.temporary_application, 1)?
            else {
                return Ok(None);
            };
            let selected_check = verification
                .selected_fact_check
                .factual_success()
                .ok_or_else(|| "by-thm selected-fact check is not factual".to_string())?;
            let selected_fact: Fact = verification.selected_fact.clone().into();
            if selected_check.fact().to_string() != selected_fact.to_string()
                || !selected_check.store.infers.is_empty()
            {
                return Err("by-thm selected-fact check changed its target or effects".into());
            }
            let Some(selected_proof) =
                self.construct_lean_proof_from_direct_fact_result(selected_check)?
            else {
                return Ok(None);
            };
            proof_lines.push(format!("exact {selected_proof}"));
            let proposition = render_fact(&selected_fact, &self.environment_stack)?;
            let retained_fact_id = if result.common.infers.rule_applications.is_empty() {
                validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &selected_fact,
                    "by-thm selected parent fact",
                )?
            } else {
                validate_defined_predicate_fact_publication_effects(
                    &result.common.infers,
                    &selected_fact,
                    "by-thm selected parent fact",
                )?
            };
            Ok(Some(CompiledByTheoremSelectionProofBody {
                fact: selected_fact,
                retained_fact_id,
                proposition,
                proof_lines,
            }))
        })();
        self.environment_stack.pop_local_environment();
        compilation
    }

    /// `Combine`: construct the exact ordered theorem conclusions without
    /// publishing them into the caller's compiler environment. The enclosing
    /// statement decides whether those Result-owned FactIds become visible or
    /// remain local to another proof layer.
    pub(super) fn construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(
        &mut self,
        result: &SuccessReleaseThmStmtResult,
    ) -> Result<Option<Vec<CompiledLitexTheoremInstantiationConclusionProofBody>>, String> {
        let Some(verification) = &result.verification else {
            return Ok(None);
        };
        let SuccessVerifyTheoremApplicationSourceResult::Litex(source) = &verification.source
        else {
            return Ok(None);
        };
        if verification.theorem != result.statement.name.to_string()
            || verification.arguments.len() != result.statement.args.len()
            || verification
                .arguments
                .iter()
                .zip(result.statement.args.iter())
                .any(|(retained, source)| obj_equality_key(retained) != obj_equality_key(source))
        {
            return Err("release-thm Result changed its theorem name or argument order".into());
        }
        let source_fact_id = source
            .source_fact_id
            .ok_or_else(|| "release-thm Result has no source theorem FactId".to_string())?;
        let source_fact = self
            .environment_stack
            .fact_propositions
            .get(&source_fact_id)
            .cloned()
            .ok_or_else(|| {
                format!("release-thm cited unavailable source FactId `{source_fact_id}`")
            })?;
        let Fact::ForallFact(source_forall) = &source_fact else {
            return Err("release-thm source FactId does not identify a forall fact".into());
        };
        let source_parameters = source_forall
            .typed_parameters
            .collect_param_bindings_with_types();
        if source_parameters.iter().any(|(_, parameter_type)| {
            !matches!(parameter_type, ParamType::Obj(Obj::StandardSet(_)))
        }) {
            return Ok(None);
        }
        if source_parameters.len() != result.statement.args.len()
            || source_forall.dom_facts.len() != source.domain_facts.len()
            || source.domain_facts.len() != source.domain_checks.len()
            || source_forall.then_facts.len() != verification.direct_conclusions.len()
            || verification.direct_conclusions.is_empty()
        {
            return Err("release-thm Result changed its source theorem arity".into());
        }
        let source_substitutions = source_parameters
            .iter()
            .zip(result.statement.args.iter())
            .map(|((binding, _), argument)| (binding.id().substitution_key(), argument.clone()))
            .collect::<HashMap<_, _>>();
        let Some(argument_verification) = &source.argument_verification else {
            return Err("release-thm Result has no argument verification children".into());
        };
        if !argument_verification.infers.is_empty()
            || argument_verification.checks.len() != source_parameters.len()
        {
            return Ok(None);
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
            return Err("release-thm Result changed its direct conclusion store count".into());
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
                        "release-thm Result changed a direct conclusion store proposition".into(),
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
            .ok_or_else(|| {
                format!("release-thm source FactId `{source_fact_id}` has no Lean name")
            })?;
        let mut application_parts = vec![theorem_name];
        let mut source_parameter_rendering_aliases = Vec::with_capacity(source_parameters.len());
        for (parameter_index, (((_, parameter_type), argument), check)) in source_parameters
            .iter()
            .zip(result.statement.args.iter())
            .zip(argument_verification.checks.iter())
            .enumerate()
        {
            let parameter_set = parameter_set(parameter_type)
                .map_err(|error| format!("release-thm parameter {parameter_index}: {error}"))?;
            let native_integer_parameter =
                matches!(parameter_set, Obj::StandardSet(StandardSet::Z));
            let rendered_argument = render_obj(argument, &self.environment_stack)?;
            let expected_parameter_fact = format!(
                "Litex.In {rendered_argument} {}",
                render_obj(parameter_set, &self.environment_stack)?
            );
            let factual_check = check.factual_success().ok_or_else(|| {
                format!("release-thm argument check {parameter_index} is not factual")
            })?;
            if render_fact(&factual_check.fact(), &self.environment_stack)?
                != expected_parameter_fact
                || !factual_check.store.infers.is_empty()
            {
                return Err(format!(
                    "release-thm argument check {parameter_index} changed its parameter obligation"
                ));
            }
            let Some(parameter_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            let native_integer_argument = if native_integer_parameter {
                Some(render_integer_obj(argument, &self.environment_stack)?)
            } else {
                None
            };
            application_parts.push(
                native_integer_argument
                    .clone()
                    .unwrap_or_else(|| rendered_argument.clone()),
            );
            if !native_integer_parameter {
                application_parts.push(format!("({parameter_proof})"));
            }
            source_parameter_rendering_aliases.push((
                source_parameters[parameter_index].0.id(),
                parameter_set.clone(),
                render_obj(argument, &self.environment_stack)?,
                parameter_proof,
                native_integer_argument,
            ));
        }
        let mut instantiator = Runtime::default();
        // Capture-avoiding substitution for existential conclusions consults
        // the Runtime's visible-definition frame even though compilation does
        // not execute or search for any proof. Give this isolated structural
        // instantiator the same mandatory empty frame as an ordinary source.
        instantiator.start_isolated_source("stmt-result-to-lean release-thm projection");
        for (domain_index, ((source_domain, retained_domain), check)) in source_forall
            .dom_facts
            .iter()
            .zip(source.domain_facts.iter())
            .zip(source.domain_checks.iter())
            .enumerate()
        {
            let expected_domain = instantiator
                .inst_fact(
                    source_domain,
                    &source_substitutions,
                    SubstitutionMode::Named,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "release-thm could not instantiate domain {domain_index}: {}",
                        error.trace_message()
                    )
                })?;
            if expected_domain.to_string() != retained_domain.to_string() {
                return Err(format!(
                    "release-thm domain {domain_index} changed under exact parameter substitution"
                ));
            }
            let factual_check = check
                .factual_success()
                .ok_or_else(|| format!("release-thm domain check {domain_index} is not factual"))?;
            if factual_check.fact().to_string() != retained_domain.to_string()
                || !factual_check.store.infers.is_empty()
            {
                return Err(format!(
                    "release-thm domain check {domain_index} changed its retained obligation"
                ));
            }
            let Some(domain_proof) =
                self.construct_lean_proof_from_direct_fact_result(factual_check)?
            else {
                return Ok(None);
            };
            application_parts.push(format!("({domain_proof})"));
        }
        let theorem_application = format!("({})", application_parts.join(" "));

        let mut conclusion_rendering_context = self.environment_stack.clone();
        for (
            source_symbol_id,
            parameter_set,
            rendered_argument,
            parameter_proof,
            native_integer_argument,
        ) in &source_parameter_rendering_aliases
        {
            conclusion_rendering_context
                .symbol_names
                .insert(*source_symbol_id, rendered_argument.clone());
            let lowered_set = LeanTargetObjectRepresentation::lower(parameter_set)?;
            install_numeric_representations_from_membership(
                *source_symbol_id,
                &lowered_set,
                rendered_argument,
                parameter_proof,
                &mut conclusion_rendering_context,
            );
            if let Some(native_integer_argument) = native_integer_argument {
                install_structured_induction_native_integer_symbol(
                    *source_symbol_id,
                    native_integer_argument,
                    &mut conclusion_rendering_context,
                );
            }
        }
        if let Some(mut theorem_well_definedness) = self
            .environment_stack
            .fact_well_definedness
            .get(&source_fact_id)
            .cloned()
        {
            for alias in &theorem_well_definedness.parameter_fact_aliases {
                let Some((_, _, _, parameter_proof, _)) = source_parameter_rendering_aliases
                    .iter()
                    .find(|(source_symbol_id, _, _, _, _)| *source_symbol_id == alias.symbol_id)
                else {
                    // The theorem WD tree also owns aliases for binders local
                    // to a projected conclusion (for example an existential
                    // witness). They are not theorem arguments and must stay
                    // under that conclusion's binder rather than being
                    // rebound to an application argument here.
                    continue;
                };
                conclusion_rendering_context
                    .fact_names
                    .insert(alias.fact_id, parameter_proof.clone());
                conclusion_rendering_context
                    .fact_propositions
                    .insert(alias.fact_id, alias.proposition.clone());
            }
            for application in theorem_well_definedness.function_applications.values_mut() {
                application.source_application = instantiator
                    .inst_obj(
                        &application.source_application,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| {
                        format!(
                            "release-thm could not specialize a WD application: {}",
                            error.trace_message()
                        )
                    })?;
                if let Some(head) = &application.anonymous_function_head {
                    application.anonymous_function_head = Some(
                        instantiator
                            .inst_obj(
                                head,
                                &source_substitutions,
                                SubstitutionMode::ResultProjection,
                            )
                            .map_err(|error| {
                                format!(
                                    "release-thm could not specialize an anonymous application head: {}",
                                    error.trace_message()
                                )
                            })?,
                    );
                }
                for layer in &mut application.layers {
                    layer.source_prefix = instantiator
                        .inst_obj(
                            &layer.source_prefix,
                            &source_substitutions,
                            SubstitutionMode::ResultProjection,
                        )
                        .map_err(|error| {
                            format!(
                                "release-thm could not specialize an application prefix: {}",
                                error.trace_message()
                            )
                        })?;
                    if let Some(result_set) = &layer.intrinsic_result_set {
                        layer.intrinsic_result_set = Some(
                            instantiator
                                .inst_obj(
                                    result_set,
                                    &source_substitutions,
                                    SubstitutionMode::ResultProjection,
                                )
                                .map_err(|error| {
                                    format!(
                                        "release-thm could not specialize an application return set: {}",
                                        error.trace_message()
                                    )
                                })?,
                        );
                    }
                    for requirement in &mut layer.requirements {
                        requirement.expected_proposition = instantiator
                            .inst_fact(
                                &requirement.expected_proposition,
                                &source_substitutions,
                                SubstitutionMode::ResultProjection,
                                None,
                            )
                            .map_err(|error| {
                                format!(
                                    "release-thm could not specialize an application WD requirement: {}",
                                    error.trace_message()
                                )
                            })?;
                    }
                }
            }
            for iteration in theorem_well_definedness.iterations.values_mut() {
                iteration.source_aggregate = instantiator
                    .inst_obj(
                        &iteration.source_aggregate,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| {
                        format!(
                            "release-thm could not specialize an Iteration WD owner: {}",
                            error.trace_message()
                        )
                    })?;
                iteration.parameter_set = instantiator
                    .inst_obj(
                        &iteration.parameter_set,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| error.trace_message())?;
                iteration.return_carrier = instantiator
                    .inst_obj(
                        &iteration.return_carrier,
                        &source_substitutions,
                        SubstitutionMode::ResultProjection,
                    )
                    .map_err(|error| error.trace_message())?;
            }
            conclusion_rendering_context.well_definedness = Some(theorem_well_definedness);
        }

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
            let source_conclusion = source_forall.then_facts[conclusion_index].clone().to_fact();
            let projected_conclusion = instantiator
                .inst_fact(
                    &source_conclusion,
                    &source_substitutions,
                    SubstitutionMode::ResultProjection,
                    None,
                )
                .map_err(|error| {
                    format!(
                        "release-thm could not project conclusion {conclusion_index} WD provenance: {}",
                        error.trace_message()
                    )
                })?;
            if projected_conclusion.to_string() != conclusion.to_string() {
                return Err(format!(
                    "release-thm projected conclusion {conclusion_index} changed its proposition"
                ));
            }
            let proposition = render_fact(&projected_conclusion, &conclusion_rendering_context)?;
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
        let goal_well_definedness = self.construct_well_definedness_to_lean_compilation_context(
            &verification.well_definedness,
        )?;

        self.environment_stack.push_inherited_environment();
        self.environment_stack.well_definedness = Some(goal_well_definedness);
        let compilation = (|| {
            if let Some(recursive) = verification.well_definedness.recursive.as_deref() {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    recursive,
                    &mut self.environment_stack,
                )?;
            }
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
        if let StmtResult::Success(SuccessStmtResult::ReleaseThmStmt(result)) = result {
            if let Some(verification) = &result.verification {
                if let SuccessVerifyTheoremApplicationSourceResult::Builtin(source) =
                    &verification.source
                {
                    if matches!(
                        source.theorem_id,
                        BuiltinTheoremId::RealGreatestLowerBoundExists
                            | BuiltinTheoremId::RealGreatestLowerBoundLeMember
                            | BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound
                    ) {
                        return Err(
                            "real greatest-lower-bound builtin theorems are currently Litex-kernel-only; the Lean rule adapter has not been installed"
                                .into(),
                        );
                    }
                }
            }
            let conclusions = if let Some(conclusions) =
                self.construct_lean_proofs_from_litex_theorem_instantiation_stmt_result(result)?
            {
                conclusions
            } else {
                return Ok(None);
            };
            let multiple_outputs = conclusions.len() > 1;
            let mut lines = Vec::with_capacity(conclusions.len());
            for (output_index, conclusion) in conclusions.into_iter().enumerate() {
                let fact_id = conclusion.retained_fact_id.ok_or_else(|| {
                    format!(
                        "local release-thm conclusion `{}` has no retained FactId",
                        conclusion.fact
                    )
                })?;
                let name = if multiple_outputs {
                    format!("__step{proof_step_index}_{}", output_index + 1)
                } else {
                    format!("__step{proof_step_index}")
                };
                self.environment_stack
                    .fact_names
                    .insert(fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(fact_id, conclusion.fact);
                lines.push(format!(
                    "have {name} : {} := by\n  exact {}",
                    conclusion.proposition, conclusion.proof_expression
                ));
            }
            return Ok(Some(lines));
        }
        if let StmtResult::Success(SuccessStmtResult::By(by_result)) = result {
            if let SuccessByStmtResult::ByThmStmt(result) = by_result {
                let Some(body) =
                    self.construct_lean_proof_from_by_theorem_selection_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let name = format!("__step{proof_step_index}");
                self.environment_stack
                    .fact_names
                    .insert(body.retained_fact_id, name.clone());
                self.environment_stack
                    .fact_propositions
                    .insert(body.retained_fact_id, body.fact);
                self.compile_defined_predicate_inference_results_in_current_environment(
                    &result.common.infers,
                    DefinedPredicateInferenceConclusionPublication::LocalProofExpression,
                )?;
                validate_flattened_inferred_fact_ids_are_visible(
                    &result.common.infers,
                    &self.environment_stack,
                    "local by-thm selected parent fact",
                )?;
                return Ok(Some(vec![format!(
                    "have {name} : {} := by\n{}",
                    body.proposition,
                    indent_lines(&body.proof_lines.join("\n"), 2)
                )]));
            }
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
            if let SuccessByStmtResult::ByInducStmt(result) = by_result {
                let Some(proof) = self
                    .construct_lean_proof_from_structured_integer_induction_stmt_result(result)?
                else {
                    return Ok(None);
                };
                let fact_id = validate_generated_fact_publication_effects(
                    &result.common.infers,
                    &proof.fact,
                    "local structured integer induction generated forall",
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
        let child_certificate = result
            .well_definedness
            .recursive
            .as_ref()
            .map(|_| {
                self.construct_well_definedness_to_lean_compilation_context(
                    &result.well_definedness,
                )
            })
            .transpose()?;
        let parent_certificate = child_certificate
            .map(|certificate| self.environment_stack.well_definedness.replace(certificate));
        let compiled = (|| {
            if let Some(recursive) = result.well_definedness.recursive.as_deref() {
                install_fact_well_definedness_proof_store_results_in_active_environment(
                    recursive,
                    &mut self.environment_stack,
                )?;
            }
            let proof = self.construct_lean_proof_from_direct_fact_result(result)?;
            let proposition = render_fact(&source_fact, &self.environment_stack)?;
            Ok::<_, String>((proof, proposition))
        })();
        if let Some(parent_certificate) = parent_certificate {
            self.environment_stack.well_definedness = parent_certificate;
        }
        let (Some(proof), proposition) = compiled? else {
            return Ok(None);
        };
        let name = format!("__step{proof_step_index}");
        self.environment_stack
            .fact_names
            .insert(fact_id, name.clone());
        self.environment_stack
            .fact_propositions
            .insert(fact_id, source_fact.clone());
        let mut lines = vec![format!(
            "have {name} : {proposition} := by\n  exact {proof}"
        )];
        if !result.store.infers.is_empty() {
            // Inferred conclusions belong to the same source occurrence tree
            // as the proved chain. Re-enter that exact child-owned WD frame;
            // rendering them under the enclosing theorem frame could select
            // no occurrence, or a semantically equal occurrence from another
            // proof step.
            let inference_certificate = result
                .well_definedness
                .recursive
                .as_ref()
                .map(|_| {
                    self.construct_well_definedness_to_lean_compilation_context(
                        &result.well_definedness,
                    )
                })
                .transpose()?;
            let inference_parent_certificate = inference_certificate
                .map(|certificate| self.environment_stack.well_definedness.replace(certificate));
            let inference_compilation = (|| {
                let allowed_sources = self
                    .install_equality_chain_adjacent_projections_for_typed_inference(
                        &source_fact,
                        fact_id,
                        &name,
                        &result.store.infers,
                        "local proof-step Result",
                    )?;
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

fn same_compiler_object(left: &Obj, right: &Obj) -> bool {
    obj_equality_key(left) == obj_equality_key(right)
}

fn fact_is_subset_of(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::SubsetFact(subset))
            if same_compiler_object(&subset.left, left)
                && same_compiler_object(&subset.right, right)
    )
}

fn fact_is_nonempty(set: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty))
            if same_compiler_object(&nonempty.set, set)
    )
}

fn fact_is_membership(element: &Obj, set: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::InFact(membership))
            if same_compiler_object(&membership.element, element)
                && same_compiler_object(&membership.set, set)
    )
}

fn fact_is_less(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::LessFact(less))
            if same_compiler_object(&less.left, left)
                && same_compiler_object(&less.right, right)
    )
}

fn fact_is_less_equal(left: &Obj, right: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(AtomicFact::LessEqualFact(less_equal))
            if same_compiler_object(&less_equal.left, left)
                && same_compiler_object(&less_equal.right, right)
    )
}

fn atomic_is_real_lub_certificate(set: &Obj, candidate: &Obj, fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NormalAtomicFact(certificate)
            if certificate.predicate.to_string() == IS_REAL_LEAST_UPPER_BOUND
                && certificate.body.len() == 2
                && same_compiler_object(&certificate.body[0], set)
                && same_compiler_object(&certificate.body[1], candidate)
    )
}

fn fact_is_real_lub_certificate(set: &Obj, candidate: &Obj, fact: &Fact) -> bool {
    matches!(
        fact,
        Fact::AtomicFact(atomic)
            if atomic_is_real_lub_certificate(set, candidate, atomic)
    )
}

fn fact_is_real_upper_bound_forall(set: &Obj, upper_bound: &Obj, fact: &Fact) -> bool {
    let Fact::ForallFact(forall) = fact else {
        return false;
    };
    let [group] = forall.typed_parameters.groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let real: Obj = StandardSet::R.into();
    if !same_compiler_object(parameter_set, &real) {
        return false;
    }
    let member = obj_for_bound_param_in_scope(binding);
    let [domain] = forall.dom_facts.as_slice() else {
        return false;
    };
    let [conclusion] = forall.then_facts.as_slice() else {
        return false;
    };
    let ExistOrAndChainAtomicFact::AtomicFact(conclusion) = conclusion else {
        return false;
    };
    fact_is_membership(&member, set, domain)
        && matches!(
            conclusion,
            AtomicFact::LessEqualFact(less_equal)
                if same_compiler_object(&less_equal.left, &member)
                    && same_compiler_object(&less_equal.right, upper_bound)
        )
}

fn validate_real_lub_existential(set: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let real: Obj = StandardSet::R.into();
    if !same_compiler_object(parameter_set, &real) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AtomicFact(body) = body else {
        return false;
    };
    atomic_is_real_lub_certificate(set, &obj_for_bound_param_in_scope(binding), body)
}

fn validate_rational_between_existential(left: &Obj, right: &Obj, conclusion: &Fact) -> bool {
    let Fact::ExistFact(existential) = conclusion else {
        return false;
    };
    if !existential.is_plain_exist() {
        return false;
    }
    let [group] = existential.typed_parameters().groups.as_slice() else {
        return false;
    };
    let [binding] = group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &group.param_type else {
        return false;
    };
    let rationals: Obj = StandardSet::Q.into();
    if !same_compiler_object(parameter_set, &rationals) {
        return false;
    }
    let [body] = existential.facts().as_slice() else {
        return false;
    };
    let QuantifierFreeFact::AndFact(body) = body else {
        return false;
    };
    let [left_less, right_less] = body.facts.as_slice() else {
        return false;
    };
    let rational = obj_for_bound_param_in_scope(binding);
    matches!(
        left_less,
        AtomicFact::LessFact(less)
            if same_compiler_object(&less.left, left)
                && same_compiler_object(&less.right, &rational)
    ) && matches!(
        right_less,
        AtomicFact::LessFact(less)
            if same_compiler_object(&less.left, &rational)
                && same_compiler_object(&less.right, right)
    )
}

fn validate_real_analysis_builtin_contract(
    theorem_id: BuiltinTheoremId,
    arguments: &[Obj],
    requirements: &[Fact],
    conclusion: &Fact,
) -> Result<(), String> {
    let real: Obj = StandardSet::R.into();
    let valid = match theorem_id {
        BuiltinTheoremId::RealLeastUpperBoundExists => {
            let ([set, upper_bound], [subset, nonempty, upper_real, upper_forall]) =
                (arguments, requirements)
            else {
                return Err("real LUB existence Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_nonempty(set, nonempty)
                && fact_is_membership(upper_bound, &real, upper_real)
                && fact_is_real_upper_bound_forall(set, upper_bound, upper_forall)
                && validate_real_lub_existential(set, conclusion)
        }
        BuiltinTheoremId::RealMemberLeLeastUpperBound => {
            let ([set, candidate, member], [subset, candidate_real, certificate, membership]) =
                (arguments, requirements)
            else {
                return Err("real LUB member projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_lub_certificate(set, candidate, certificate)
                && fact_is_membership(member, set, membership)
                && fact_is_less_equal(member, candidate, conclusion)
        }
        BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => {
            let (
                [set, candidate, upper_bound],
                [subset, candidate_real, certificate, upper_real, upper_forall],
            ) = (arguments, requirements)
            else {
                return Err("real LUB upper-bound projection Result changed its arity".into());
            };
            fact_is_subset_of(set, &real, subset)
                && fact_is_membership(candidate, &real, candidate_real)
                && fact_is_real_lub_certificate(set, candidate, certificate)
                && fact_is_membership(upper_bound, &real, upper_real)
                && fact_is_real_upper_bound_forall(set, upper_bound, upper_forall)
                && fact_is_less_equal(candidate, upper_bound, conclusion)
        }
        BuiltinTheoremId::RationalBetweenReals => {
            let ([left, right], [left_real, right_real, ordered]) = (arguments, requirements)
            else {
                return Err("rational density Result changed its arity".into());
            };
            fact_is_membership(left, &real, left_real)
                && fact_is_membership(right, &real, right_real)
                && fact_is_less(left, right, ordered)
                && validate_rational_between_existential(left, right, conclusion)
        }
        _ => return Err("non-analysis theorem reached real-analysis validator".into()),
    };
    if valid {
        Ok(())
    } else {
        Err("real-analysis builtin theorem changed its structural fact contract".into())
    }
}

fn builtin_theorem_requirement_roles(
    theorem_id: BuiltinTheoremId,
) -> Vec<BuiltinTheoremRequirementRole> {
    use BuiltinTheoremRequirementRole as Role;
    match theorem_id {
        BuiltinTheoremId::SubsetOfFiniteSetIsFinite => vec![
            Role::FirstArgumentIsSet,
            Role::SecondArgumentIsFiniteSet,
            Role::FirstArgumentSubsetOfSecond,
        ],
        BuiltinTheoremId::FiniteSetHasBijectiveIndex => vec![Role::ArgumentIsFiniteSet],
        BuiltinTheoremId::RationalHasUniqueReducedFraction => {
            vec![Role::ArgumentBelongsToRationals]
        }
        BuiltinTheoremId::FunctionSetMember => vec![Role::FunctionSignatureMatchesTarget],
        BuiltinTheoremId::SetBuilderMember => vec![Role::SetBuilderDefiningFacts],
        BuiltinTheoremId::DefinedSetMember => vec![Role::DefinedSetMembership],
        BuiltinTheoremId::StructMember => vec![Role::StructCarrierFacts],
        BuiltinTheoremId::CartesianMemberFromCoordinates => vec![Role::CartesianCoordinates],
        BuiltinTheoremId::GeneralCartesianMember => {
            vec![Role::GeneralCartesianPointwiseMembership]
        }
        BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromFamily => {
            vec![Role::GeneralCartesianFamilyNonempty]
        }
        BuiltinTheoremId::GeneralCartesianNonemptyByChoiceFromPointwise => {
            vec![Role::GeneralCartesianPointwiseNonempty]
        }
        BuiltinTheoremId::SumLessEqualFromPointwise => vec![Role::IntegerSumPointwiseOrder],
        BuiltinTheoremId::FiniteSetSumLessEqualFromPointwise => {
            vec![Role::FiniteSetSumPointwiseOrder]
        }
        BuiltinTheoremId::FiniteSetSummandLessEqualSum => {
            vec![Role::FiniteSetSummandNonnegative]
        }
        BuiltinTheoremId::TupleEqualFromCoordinates => vec![Role::TupleCoordinatesEqual],
        BuiltinTheoremId::FiniteSetSumSubstitution => vec![Role::FiniteSetSumSubstitution],
        BuiltinTheoremId::SumOverBijectiveFiniteSetEnumerations => {
            vec![Role::BijectiveFiniteSetEnumerations]
        }
        BuiltinTheoremId::RealLeastUpperBoundExists => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::ArgumentSetIsNonempty,
            Role::SuppliedUpperBoundBelongsToReals,
            Role::SuppliedValueBoundsEverySetMember,
        ],
        BuiltinTheoremId::RealMemberLeLeastUpperBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealLeastUpperBound,
            Role::ArgumentIsMemberOfSet,
        ],
        BuiltinTheoremId::RealLeastUpperBoundLeUpperBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealLeastUpperBound,
            Role::SuppliedUpperBoundBelongsToReals,
            Role::SuppliedValueBoundsEverySetMember,
        ],
        BuiltinTheoremId::RealGreatestLowerBoundExists => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::ArgumentSetIsNonempty,
            Role::SuppliedLowerBoundBelongsToReals,
            Role::SuppliedValueIsLowerBoundForEverySetMember,
        ],
        BuiltinTheoremId::RealGreatestLowerBoundLeMember => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealGreatestLowerBound,
            Role::ArgumentIsMemberOfSet,
        ],
        BuiltinTheoremId::RealLowerBoundLeGreatestLowerBound => vec![
            Role::ArgumentSetSubsetOfReals,
            Role::CandidateBelongsToReals,
            Role::CandidateIsRealGreatestLowerBound,
            Role::SuppliedLowerBoundBelongsToReals,
            Role::SuppliedValueIsLowerBoundForEverySetMember,
        ],
        BuiltinTheoremId::RationalBetweenReals => vec![
            Role::LeftArgumentBelongsToReals,
            Role::RightArgumentBelongsToReals,
            Role::RealArgumentsStrictlyOrdered,
        ],
    }
}
