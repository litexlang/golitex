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
    /// body as a named theorem. Strategy activation is a Runtime concern; the
    /// generated Lean declaration is the proved forall fact stored by the
    /// statement. The recursive Result, rather than Runtime state, owns the
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

            let SuccessStmtResult::DefObjStmt(SuccessDefObjStmtResult::HaveObjEqualStmt(body)) =
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
            .params_def_with_type
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
                conclusion_type: conjunction(&conclusion_types),
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
            .params_def_with_type
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
        if let StmtResult::Success(SuccessStmtResult::DefObjStmt(
            SuccessDefObjStmtResult::LetObjStmt(result),
        )) = result
        {
            return self.compile_let_obj_stmt_result_as_local_proof_steps(result, proof_step_index);
        }
        if let StmtResult::Success(SuccessStmtResult::Command(
            SuccessCommandStmtResult::DoNothingStmt(result),
        )) = result
        {
            if !result.common.infers.is_empty() {
                return Err("local `do_nothing` unexpectedly published effects".into());
            }
            return Ok(Some(Vec::new()));
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
            .insert(defining_equality_fact_id, defining_equality);

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

    /// Returns `None` when the factual proof family explicitly carries a
    /// diagnostic-only Result or has no implemented Lean consumer. A matched
    /// typed certificate that is internally inconsistent is an error, never a
    /// fallback selected from its label.
    pub(super) fn construct_lean_proof_from_direct_fact_result(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<Option<String>, String> {
        let source_fact = result.fact();
        match result.proof() {
            SuccessFactProofResult::StoredFactCitation(citation) => {
                self.construct_lean_stored_fact_citation_proof_from_result(&source_fact, citation)
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => self
                .construct_lean_checked_function_definition_reduction_from_result(
                    &source_fact,
                    &result.verification,
                )
                .map(Some),
            SuccessFactProofResult::Strategy(_)
            | SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => Ok(None),
            SuccessFactProofResult::BuiltinRule(builtin)
            | SuccessFactProofResult::BuiltinStrategy(builtin) => {
                if let Some(BuiltinRuleEvidence::ListSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_list_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RefinedNumericMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_refined_numeric_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::NotEqualSymmetry)
                ) {
                    return self.construct_lean_not_equal_symmetry_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) =
                        builtin.evidence.typed()
                    else {
                        unreachable!("disjunction evidence checked above")
                    };
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_builder_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_application_return_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_local_builtin_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Arithmetic(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_arithmetic_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_real_arithmetic_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegerMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integer_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::NaturalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_natural_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RationalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_rational_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Set(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_set_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::KnownEqualityPath(evidence)) =
                    builtin.evidence.typed()
                {
                    return Ok(Some(self.construct_lean_known_equality_path_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    )?));
                }
                if let Some(BuiltinRuleEvidence::SetRelationDuality(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_relation_duality_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    if !builtin.subgoals.is_empty() {
                        return Err(
                            "registered reflexive-predicate proof retained child Results".into(),
                        );
                    }
                    return Ok(Some(
                        construct_lean_registered_reflexive_predicate_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    ));
                }
                if let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_symmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_antisymmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_complex_algebraic_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(evidence) = builtin.evidence.typed() {
                    if let Some(limitation) = direct_builtin_rule_compiler_limitation(evidence) {
                        return Err(limitation.to_string());
                    }
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match builtin.evidence.typed() {
                    Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("object-reflexivity evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "object-reflexivity evidence targets a non-equality fact".into()
                            );
                        };
                        if obj_equality_key(&equality.left) != obj_equality_key(&equality.right) {
                            return Err(
                                "object-reflexivity evidence changed its equality endpoints".into(),
                            );
                        }
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        let rendered_object = if result.well_definedness.recursive.is_some() {
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.left,
                            )?
                        } else {
                            render_obj(&equality.left, &self.environment_stack)?
                        };
                        Ok(Some(format!("Litex.Same.refl {rendered_object}")))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err("rational-normalization evidence changed its target".into());
                        }
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "rational-normalization evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if obj_equality_key(&equality.left)
                            != obj_equality_key(&evidence.left_evaluation.expression)
                            || obj_equality_key(&equality.right)
                                != obj_equality_key(&evidence.right_evaluation.expression)
                        {
                            return Err(
                                "rational-normalization evidence changed an equality endpoint"
                                    .into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "rational-normalization evidence retained unequal normal forms"
                                    .into(),
                            );
                        }
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        if result.well_definedness.recursive.is_some() {
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.left,
                            )?;
                            self.render_object_using_well_definedness_from_fact_result(
                                result,
                                &equality.right,
                            )?;
                        } else {
                            render_obj(&equality.left, &self.environment_stack)?;
                            render_obj(&equality.right, &self.environment_stack)?;
                        }
                        Ok(Some(
                            "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                                .into(),
                        ))
                    }
                    Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) => {
                        self.construct_lean_complex_algebraic_normalization_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "closed-numeric-membership evidence changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericNonmembership(evidence)) => {
                        if result.well_definedness.recursive.is_some() {
                            validate_atomic_fact_well_definedness_result(
                                &result.well_definedness,
                                &source_fact,
                            )?;
                        }
                        self.construct_lean_closed_numeric_nonmembership_from_result(
                            &source_fact,
                            evidence,
                        )
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        validate_closed_numeric_comparison_builtin_rule_evidence(
                            &source_fact,
                            evidence,
                        )?;
                        Ok(Some(render_closed_numeric_comparison_fact(
                            &source_fact,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::OrderReflexivity(evidence)) => Ok(Some(
                        construct_lean_order_reflexivity_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence)) => self
                        .construct_lean_runtime_resolved_numeric_comparison_from_assignment_result(
                            &source_fact,
                            evidence,
                        )
                        .map(Some),
                    Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) => Ok(Some(
                        self.construct_lean_standard_set_nonempty_from_result(
                            &source_fact,
                            evidence,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::NativeConstantMembership(rule)) => Ok(Some(
                        self.construct_lean_native_constant_membership_from_result(
                            &source_fact,
                            *rule,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::StandardSetSubset) => Ok(Some(
                        self.construct_lean_standard_set_subset_from_result(&source_fact)?,
                    )),
                    Some(BuiltinRuleEvidence::PrimeU64Reflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            true,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::CoprimeNaturalReflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            false,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::FiniteSet(rule)) => Ok(Some(
                        self.construct_lean_finite_set_from_result(&source_fact, *rule)?,
                    )),
                    Some(BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule)) => Ok(
                        Some(self.construct_lean_complex_membership_closure_from_result(
                            &source_fact,
                            *rule,
                        )?),
                    ),
                    Some(BuiltinRuleEvidence::TupleLiteralShape) => Ok(Some(
                        self.construct_lean_tuple_literal_shape_from_result(&source_fact)?,
                    )),
                    None => Ok(None),
                    Some(evidence) => unreachable!(
                        "typed builtin evidence must be handled before the terminal direct compiler dispatch: {evidence:?}"
                    ),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::KnownForallInstantiation(instantiation) => self
                .construct_lean_known_forall_instantiation_from_result(&source_fact, instantiation),
            SuccessFactProofResult::Transform(transformation) => self
                .construct_lean_single_fact_transformation_from_result(
                    &source_fact,
                    transformation,
                ),
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            // A statement-level `ForallProof` owns a compiler environment and
            // is consumed by `compile_direct_forall_fact_result`, not by this
            // proof-expression constructor.
            SuccessFactProofResult::ForallProof(_) => Ok(None),
        }
    }

    /// Temporarily exposes this statement's retained WD tree while its proof
    /// Result renders objects. Nested callers that already own a binder/WD
    /// environment keep that environment unchanged.
    pub(super) fn construct_lean_proof_from_direct_fact_result_using_its_well_definedness(
        &mut self,
        result: &SuccessFactStmtResult,
    ) -> Result<Option<String>, String> {
        if self.environment_stack.well_definedness.is_some()
            || result.well_definedness.recursive.is_none()
        {
            return self.construct_lean_proof_from_direct_fact_result(result);
        }

        let certificate =
            self.construct_well_definedness_to_lean_compilation_context(&result.well_definedness)?;
        self.environment_stack.well_definedness = Some(certificate);
        let construction = self.construct_lean_proof_from_direct_fact_result(result);
        self.environment_stack.well_definedness = None;
        construction
    }

    /// `Wrap`: compile the exact selected-equality child and inject its right
    /// endpoint into the retained list-set position. The selected index is
    /// verifier-owned evidence; neither the diagnostic label nor a search of
    /// the current environment participates.
    pub(super) fn construct_lean_list_set_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &ListSetMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [equality_result] = subgoals else {
            return Err("list-set membership requires exactly one equality child Result".into());
        };
        let equality_result = equality_result
            .factual_success()
            .ok_or_else(|| "list-set membership child Result is not factual".to_string())?;
        if !equality_result.store.infers.is_empty() {
            return Err("list-set membership equality child published effects".into());
        }

        let (element, set) = membership_parts(target)?;
        let Obj::ListSet(list_set) = set else {
            return Err("list-set membership evidence targets another set constructor".into());
        };
        let selected = list_set
            .list
            .get(evidence.selected_index)
            .ok_or_else(|| "list-set membership evidence has an out-of-range index".to_string())?;
        let equality_fact = equality_result.fact();
        if equality_result.store.fact.to_string() != equality_fact.to_string() {
            return Err("list-set membership equality child changed its stored fact".into());
        }
        let (equality_left, equality_right) = equality_parts(&equality_fact)?;
        if obj_equality_key(equality_left) != obj_equality_key(element)
            || obj_equality_key(equality_right) != obj_equality_key(selected.as_ref())
        {
            return Err("list-set membership equality changed its selected source element".into());
        }
        let Some(equality_proof) =
            self.construct_lean_proof_from_direct_fact_result(equality_result)?
        else {
            return Ok(None);
        };
        let selected_term = render_obj(selected.as_ref(), &self.environment_stack)?;
        render_obj(set, &self.environment_stack)?;
        let (witness, representation) =
            render_list_set_representation_bridge(&selected_term, evidence.selected_index);
        Ok(Some(format!(
            "⟨{witness}, Litex.Same.trans ({equality_proof}) ({representation})⟩"
        )))
    }

    /// `Combine`: construct one exact nonzero numeric carrier from the
    /// verifier-owned base-membership and nonzero child Results.
    pub(super) fn construct_lean_refined_numeric_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &RefinedNumericMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("refined numeric membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("refined numeric membership lost an ordered child Result".into());
        }
        let [base_result, nonzero_result] = subgoals else {
            return Err("refined numeric membership requires exactly two child Results".into());
        };
        let [expected_base, expected_nonzero] = evidence.expected_premises.as_slice() else {
            return Err("refined numeric membership evidence changed its premise arity".into());
        };
        let base_result = base_result
            .factual_success()
            .ok_or_else(|| "refined numeric base child is not factual".to_string())?;
        let nonzero_result = nonzero_result
            .factual_success()
            .ok_or_else(|| "refined numeric nonzero child is not factual".to_string())?;
        for (name, result, expected) in [
            ("base", base_result, expected_base),
            ("nonzero", nonzero_result, expected_nonzero),
        ] {
            if result.fact().to_string() != expected.to_string()
                || result.store.fact.to_string() != expected.to_string()
                || !result.store.infers.is_empty()
            {
                return Err(format!(
                    "refined numeric {name} child changed its fact or published effects"
                ));
            }
        }

        let (target_element, target_set) = membership_parts(target)?;
        let (base_element, base_set) = membership_parts(expected_base)?;
        let (nonzero_left, nonzero_right) = not_equal_parts(expected_nonzero)?;
        if obj_equality_key(target_element) != obj_equality_key(base_element)
            || obj_equality_key(target_element) != obj_equality_key(nonzero_left)
            || !matches!(nonzero_right, Obj::Number(number) if number.normalized_value == "0")
        {
            return Err("refined numeric membership changed its source element".into());
        }
        let theorem = match (target_set, base_set) {
            (Obj::StandardSet(StandardSet::ZStar), Obj::StandardSet(StandardSet::Z)) => {
                "inZStarOfInZNotSameZero"
            }
            (Obj::StandardSet(StandardSet::QStar), Obj::StandardSet(StandardSet::Q)) => {
                "inQStarOfInQNotSameZero"
            }
            (Obj::StandardSet(StandardSet::RStar), Obj::StandardSet(StandardSet::R)) => {
                "inRStarOfInRNotSameZero"
            }
            (Obj::StandardSet(StandardSet::CStar), Obj::StandardSet(StandardSet::C)) => {
                "inCStarOfInCNotSameZero"
            }
            _ => return Ok(None),
        };
        let Some(base_proof) = self.construct_lean_proof_from_direct_fact_result(base_result)?
        else {
            return Ok(None);
        };
        let Some(nonzero_proof) =
            self.construct_lean_proof_from_direct_fact_result(nonzero_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!(
            "Litex.Rules.{theorem} ({base_proof}) ({nonzero_proof})"
        )))
    }

    /// `Leaf`: the currently reviewed closed nonmembership fragment is zero
    /// excluded from one of the exact nonzero numeric carriers. The recursive
    /// evaluation Result proves that the source expression normalized to zero.
    pub(super) fn construct_lean_closed_numeric_nonmembership_from_result(
        &self,
        target: &Fact,
        evidence: &ClosedNumericNonmembershipBuiltinRuleEvidence,
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("closed numeric nonmembership evidence changed its target".into());
        }
        validate_success_evaluate_obj_result(&evidence.evaluation)?;
        let (element, set) = nonmembership_parts(target)?;
        let Obj::StandardSet(target_set) = set else {
            return Err("closed numeric nonmembership targets a nonstandard set".into());
        };
        if *target_set != evidence.target_set
            || obj_equality_key(element) != obj_equality_key(&evidence.evaluation.expression)
        {
            return Err(
                "closed numeric nonmembership changed its expression or target carrier".into(),
            );
        }
        if evidence.evaluation.value.normalized_value != "0" {
            return Ok(None);
        }
        let theorem = match target_set {
            StandardSet::ZStar => "notSameZeroOfInZStar",
            StandardSet::QStar => "notSameZeroOfInQStar",
            StandardSet::RStar => "notSameZeroOfInRStar",
            StandardSet::CStar => "notSameZeroOfInCStar",
            _ => return Ok(None),
        };
        let source = render_obj(element, &self.environment_stack)?;
        Ok(Some(format!(
            "(fun __membership => (Litex.Rules.{theorem} (__membership)) (Litex.Same.refl {source}))"
        )))
    }

    /// `Leaf`: replay a verifier-owned canonical witness for one base standard
    /// set. The evidence fixes both the proposition and the carrier.
    pub(super) fn construct_lean_standard_set_nonempty_from_result(
        &self,
        target: &Fact,
        evidence: &StandardSetNonemptyBuiltinRuleEvidence,
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("standard-set nonempty evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = target else {
            return Err("standard-set nonempty evidence targets another fact family".into());
        };
        let Obj::StandardSet(target_set) = &nonempty.set else {
            return Err("standard-set nonempty evidence targets a nonstandard carrier".into());
        };
        if *target_set != evidence.target_set {
            return Err("standard-set nonempty evidence changed its carrier".into());
        }
        render_fact(target, &self.environment_stack)?;
        let theorem = match target_set {
            StandardSet::N => "naturalNonempty",
            StandardSet::Z => "integerNonempty",
            StandardSet::Q => "rationalNonempty",
            StandardSet::R => "realNonempty",
            StandardSet::C => "complexNonempty",
            unsupported => {
                return Err(format!(
                    "unsupported direct standard-set nonempty carrier `{unsupported}`"
                ));
            }
        };
        Ok(format!("Litex.Rules.{theorem}"))
    }

    /// `Leaf`: map the exact native constant/carrier pair to its reviewed Lean
    /// theorem. There are no premises and no diagnostic-label dispatch.
    pub(super) fn construct_lean_native_constant_membership_from_result(
        &self,
        target: &Fact,
        rule: NativeConstantMembershipBuiltinRule,
    ) -> Result<String, String> {
        let (element, set) = membership_parts(target)?;
        render_fact(target, &self.environment_stack)?;
        let theorem = match (rule, element, set) {
            (
                NativeConstantMembershipBuiltinRule::ImaginaryUnitInComplex,
                Obj::ImaginaryUnit(_),
                Obj::StandardSet(StandardSet::C),
            ) => "imaginaryUnitInC",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInReal,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::R),
            ) => "eInR",
            (
                NativeConstantMembershipBuiltinRule::PiInReal,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::R),
            ) => "piInR",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInPositiveReal,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::RPos),
            ) => "eInRPos",
            (
                NativeConstantMembershipBuiltinRule::PiInPositiveReal,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::RPos),
            ) => "piInRPos",
            (
                NativeConstantMembershipBuiltinRule::EulerNumberInComplex,
                Obj::EulerNumber(_),
                Obj::StandardSet(StandardSet::C),
            ) => "inCOfInR (Litex.Rules.eInR)",
            (
                NativeConstantMembershipBuiltinRule::PiInComplex,
                Obj::Pi(_),
                Obj::StandardSet(StandardSet::C),
            ) => "inCOfInR (Litex.Rules.piInR)",
            _ => return Err("native constant membership changed its constant or carrier".into()),
        };
        Ok(format!("Litex.Rules.{theorem}"))
    }

    /// `Wrap`: compile the sole reversed disequality child and apply symmetry.
    pub(super) fn construct_lean_not_equal_symmetry_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [source_result] = subgoals else {
            return Err("not-equality symmetry requires exactly one child Result".into());
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "not-equality symmetry child is not factual".to_string())?;
        if !source_result.store.infers.is_empty() {
            return Err("not-equality symmetry child published effects".into());
        }
        let source = source_result.fact();
        let (target_left, target_right) = not_equal_parts(target)?;
        let (source_left, source_right) = not_equal_parts(&source)?;
        if obj_equality_key(source_left) != obj_equality_key(target_right)
            || obj_equality_key(source_right) != obj_equality_key(target_left)
        {
            return Err("not-equality symmetry child does not reverse the target objects".into());
        }
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!("Litex.Rules.notSameSymm ({source_proof})")))
    }

    /// `Leaf`: construct a subset function from the fixed standard-set
    /// inclusion chain encoded by the target endpoints.
    pub(super) fn construct_lean_standard_set_subset_from_result(
        &self,
        target: &Fact,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::SubsetFact(subset)) = target else {
            return Err("standard-set subset evidence targets another fact family".into());
        };
        let (Obj::StandardSet(source), Obj::StandardSet(destination)) =
            (&subset.left, &subset.right)
        else {
            return Err("standard-set subset evidence retained a nonstandard endpoint".into());
        };
        render_fact(target, &self.environment_stack)?;
        if source == destination {
            return Ok("(fun _x hx => hx)".into());
        }
        let mut proof = "hx".to_string();
        for theorem in standard_set_membership_projection_theorem_chain(*source, *destination)? {
            proof = format!("Litex.Rules.{theorem} ({proof})");
        }
        Ok(format!("(fun _x hx => {proof})"))
    }

    /// `Leaf`: replay closed prime/coprime reflection after validating the
    /// exact predicate, arity, and natural-literal boundary.
    pub(super) fn construct_lean_number_theory_reflection_from_result(
        &self,
        target: &Fact,
        is_prime_rule: bool,
    ) -> Result<String, String> {
        let (predicate, arguments, negated) = match target {
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(value)) => {
                (value.predicate.to_string(), value.body.as_slice(), false)
            }
            Fact::AtomicFact(AtomicFact::NotNormalAtomicFact(value)) => {
                (value.predicate.to_string(), value.body.as_slice(), true)
            }
            _ => return Err("number-theory reflection retained a non-predicate target".into()),
        };
        let (expected_predicate, expected_arity) = if is_prime_rule {
            (PRIME, 1)
        } else {
            (COPRIME, 2)
        };
        if predicate != expected_predicate || arguments.len() != expected_arity {
            return Err("number-theory reflection changed its predicate or arity".into());
        }
        let mut values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let Obj::Number(number) = argument else {
                return Err("number-theory reflection changed a closed numeric argument".into());
            };
            if number.normalized_value.starts_with('-')
                || number.normalized_value.contains('.')
                || (is_prime_rule && number.normalized_value.parse::<u64>().is_err())
            {
                return Err("number-theory reflection retained a non-natural argument".into());
            }
            values.push(number.normalized_value.as_str());
        }
        render_fact(target, &self.environment_stack)?;
        if is_prime_rule {
            let theorem = if negated {
                "notPrimeOfNat"
            } else {
                "primeOfNat"
            };
            Ok(format!(
                "(by simpa using (Litex.{theorem} {} (by norm_num)))",
                values[0]
            ))
        } else {
            let theorem = if negated {
                "notCoprimeOfNat"
            } else {
                "coprimeOfNat"
            };
            Ok(format!(
                "(by simpa using (Litex.{theorem} {} {} (by norm_num)))",
                values[0], values[1]
            ))
        }
    }

    /// `Leaf`: construct finiteness from the exact set constructor retained by
    /// the target proposition.
    pub(super) fn construct_lean_finite_set_from_result(
        &self,
        target: &Fact,
        rule: FiniteSetBuiltinRule,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(finite)) = target else {
            return Err("finite-set evidence targets a non-finiteness fact".into());
        };
        render_fact(target, &self.environment_stack)?;
        match (rule, &finite.set) {
            (FiniteSetBuiltinRule::Range, Obj::Range(_)) => {
                Ok("(by unfold Litex.Set.Finite Litex.range; infer_instance)".into())
            }
            (FiniteSetBuiltinRule::ClosedRange, Obj::ClosedRange(_)) => {
                Ok("(by unfold Litex.Set.Finite Litex.closedRange; infer_instance)".into())
            }
            (FiniteSetBuiltinRule::ListSet, Obj::ListSet(list_set)) => render_list_set_finiteness(
                &list_set
                    .list
                    .iter()
                    .map(|item| LeanTargetObjectRepresentation::lower(item.as_ref()))
                    .collect::<Result<Vec<_>, _>>()?,
                &self.environment_stack,
            ),
            _ => Err("finite-set evidence changed its exact constructor family".into()),
        }
    }

    /// `Leaf`: complex arithmetic is closed without operand premises because
    /// every target-selected operand representation has the universal complex
    /// view. A binder may select `In.rep` instead of the heterogeneous source
    /// symbol, so this must render the numeric view used by the target.
    pub(super) fn construct_lean_complex_membership_closure_from_result(
        &self,
        target: &Fact,
        rule: ComplexArithmeticMembershipClosureBuiltinRule,
    ) -> Result<String, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::C)) {
            return Err("complex arithmetic membership target is not C".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (ComplexArithmeticMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Sub, Obj::Sub(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexSubInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInC",
            ),
            (ComplexArithmeticMembershipClosureBuiltinRule::Div, Obj::Div(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexDivInC",
            ),
            _ => return Err("complex arithmetic membership changed its operator".into()),
        };
        let rendered_left = render_numeric_obj(left, &self.environment_stack)?;
        let rendered_right = render_numeric_obj(right, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_target = format!(
            "Litex.In ({rendered_left} {} {rendered_right}) Litex.C",
            match rule {
                ComplexArithmeticMembershipClosureBuiltinRule::Add => "+",
                ComplexArithmeticMembershipClosureBuiltinRule::Sub => "-",
                ComplexArithmeticMembershipClosureBuiltinRule::Mul => "*",
                ComplexArithmeticMembershipClosureBuiltinRule::Div => "/",
            }
        );
        if rendered_target != expected_target {
            return Err("complex arithmetic rendering changed its verified target".into());
        }
        Ok(format!(
            "Litex.Rules.{theorem} {rendered_left} {rendered_right}"
        ))
    }

    /// `Leaf`: tuple syntax itself fixes the reflected tuple-shape instance.
    /// The verifier attaches this certificate only after checking the literal
    /// has the tuple arity accepted by the source language.
    pub(super) fn construct_lean_tuple_literal_shape_from_result(
        &self,
        target: &Fact,
    ) -> Result<String, String> {
        let Fact::AtomicFact(AtomicFact::IsTupleFact(tuple_fact)) = target else {
            return Err("tuple-literal shape evidence targets another fact family".into());
        };
        let Obj::Tuple(tuple) = &tuple_fact.set else {
            return Err("tuple-literal shape evidence changed its exact object".into());
        };
        if tuple.args.len() < 2 {
            return Err("tuple-literal shape evidence retained fewer than two items".into());
        }
        render_fact(target, &self.environment_stack)?;
        Ok("⟨inferInstance⟩".into())
    }

    /// `Wrap`: the integer closure certificate owns one exact conjunction
    /// child whose ordered components prove the two operand memberships.
    pub(super) fn construct_lean_integer_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: IntegerMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Z)) {
            return Err("integer arithmetic membership target is not Z".into());
        }
        let theorem = match rule {
            IntegerMembershipClosureBuiltinRule::Add if matches!(target_element, Obj::Add(_)) => {
                "complexAddInZ"
            }
            IntegerMembershipClosureBuiltinRule::Sub if matches!(target_element, Obj::Sub(_)) => {
                "complexSubInZ"
            }
            IntegerMembershipClosureBuiltinRule::Mul if matches!(target_element, Obj::Mul(_)) => {
                "complexMulInZ"
            }
            IntegerMembershipClosureBuiltinRule::Mod if matches!(target_element, Obj::Mod(_)) => {
                return self
                    .construct_lean_integer_remainder_membership_from_result(target, subgoals);
            }
            _ => return Err("integer arithmetic closure changed its target operator".into()),
        };
        self.construct_lean_binary_membership_from_conjunction_result(
            target,
            StandardSet::Z,
            theorem,
            subgoals,
        )
    }

    /// `Wrap`: `%` owns one conjunction child proving both operands are in
    /// `Z`. The compiler validates that recursive proof, then applies the
    /// integer remainder operation to the exact representatives retained in
    /// the active compiler environment.
    pub(super) fn construct_lean_integer_remainder_membership_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Z)) {
            return Err("integer remainder membership target is not Z".into());
        }
        let Obj::Mod(remainder) = target_element else {
            return Err("integer remainder certificate changed its target operator".into());
        };
        let [conjunction_result] = subgoals else {
            return Err("integer remainder requires one conjunction child Result".into());
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "integer remainder conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("integer remainder conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [left_component, right_component] = components.as_slice() else {
            return Err("integer remainder conjunction changed its component arity".into());
        };
        for (index, (component, expected_operand)) in [left_component, right_component]
            .into_iter()
            .zip([remainder.left.as_ref(), remainder.right.as_ref()])
            .enumerate()
        {
            let (operand, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(StandardSet::Z))
                || obj_equality_key(operand) != obj_equality_key(expected_operand)
            {
                return Err(format!(
                    "integer remainder conjunction component {index} changed its operand"
                ));
            }
        }
        if self
            .construct_lean_proof_from_direct_fact_result(conjunction_result)?
            .is_none()
        {
            return Ok(None);
        }

        let left = render_integer_obj(remainder.left.as_ref(), &self.environment_stack)?;
        let right = render_integer_obj(remainder.right.as_ref(), &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let rendered_remainder = format!("(({left} % {right} : ℤ) : ℂ)");
        let expected_target = format!("Litex.In {rendered_remainder} Litex.Z");
        if rendered_target != expected_target {
            return Err("integer remainder rendering changed its verified target".into());
        }
        Ok(Some(format!(
            "Litex.Rules.complexIntInZ ({left} % {right})"
        )))
    }

    /// `Combine`: natural closure retains the two operand-membership Results
    /// directly and in source order.
    pub(super) fn construct_lean_natural_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: NaturalMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::N)) {
            return Err("natural arithmetic membership target is not N".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (NaturalMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInN",
            ),
            (NaturalMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInN",
            ),
            _ => return Err("natural arithmetic membership changed its operator".into()),
        };
        let [left_result, right_result] = subgoals else {
            return Err("natural closure requires two ordered child Results".into());
        };
        let mut proofs = Vec::with_capacity(2);
        for (index, (child, expected_element)) in [left_result, right_result]
            .into_iter()
            .zip([left, right])
            .enumerate()
        {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("natural closure child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("natural closure child {index} published effects"));
            }
            let child_fact = child.fact();
            let (element, set) = membership_parts(&child_fact)?;
            if !matches!(set, Obj::StandardSet(StandardSet::N))
                || obj_equality_key(element) != obj_equality_key(expected_element)
            {
                return Err(format!(
                    "natural closure child {index} changed its ordered operand"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            proofs.push(render_numeric_operand_membership(
                expected_element,
                &proof,
                &self.environment_stack,
            ));
        }
        Ok(Some(format!(
            "Litex.Rules.{theorem} ({}) ({})",
            proofs[0], proofs[1]
        )))
    }

    /// `Wrap`: rational closure shares the conjunction-child shape with the
    /// integer carrier. Integer power additionally switches to the exact
    /// `ℚ`/`ℤ` representatives selected in the active compiler environment.
    pub(super) fn construct_lean_rational_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: RationalMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, _) = membership_parts(target)?;
        let theorem = match rule {
            RationalMembershipClosureBuiltinRule::Add if matches!(target_element, Obj::Add(_)) => {
                "complexAddInQ"
            }
            RationalMembershipClosureBuiltinRule::Sub if matches!(target_element, Obj::Sub(_)) => {
                "complexSubInQ"
            }
            RationalMembershipClosureBuiltinRule::Mul if matches!(target_element, Obj::Mul(_)) => {
                "complexMulInQ"
            }
            RationalMembershipClosureBuiltinRule::Div if matches!(target_element, Obj::Div(_)) => {
                "complexDivInQ"
            }
            RationalMembershipClosureBuiltinRule::Pow if matches!(target_element, Obj::Pow(_)) => {
                return self.construct_lean_rational_power_membership_from_result(target, subgoals);
            }
            _ => return Err("rational arithmetic closure changed its target operator".into()),
        };
        self.construct_lean_binary_membership_from_conjunction_result(
            target,
            StandardSet::Q,
            theorem,
            subgoals,
        )
    }

    /// `Wrap`: the recursive conjunction proves `base ∈ Q` and `exponent ∈ Z`
    /// in that order. The Result supplies truth; the compiler environment only
    /// supplies the corresponding target representatives while this binder
    /// layer is active.
    pub(super) fn construct_lean_rational_power_membership_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::Q)) {
            return Err("rational power membership target is not Q".into());
        }
        let Obj::Pow(power) = target_element else {
            return Err("rational power certificate changed its target operator".into());
        };
        let [conjunction_result] = subgoals else {
            return Err("rational power requires one conjunction child Result".into());
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "rational power conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("rational power conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [base_component, exponent_component] = components.as_slice() else {
            return Err("rational power conjunction changed its component arity".into());
        };
        for (index, (component, expected_operand, expected_set)) in
            [base_component, exponent_component]
                .into_iter()
                .zip([
                    (power.base.as_ref(), StandardSet::Q),
                    (power.exponent.as_ref(), StandardSet::Z),
                ])
                .map(|(component, (operand, set))| (component, operand, set))
                .enumerate()
        {
            let (operand, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(set) if *set == expected_set)
                || obj_equality_key(operand) != obj_equality_key(expected_operand)
            {
                return Err(format!(
                    "rational power conjunction component {index} changed its operand or carrier"
                ));
            }
        }
        if self
            .construct_lean_proof_from_direct_fact_result(conjunction_result)?
            .is_none()
        {
            return Ok(None);
        }

        let base = render_rational_obj(power.base.as_ref(), &self.environment_stack)?;
        let exponent = render_integer_obj(power.exponent.as_ref(), &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let rendered_power = format!("(({base} ^ {exponent} : ℚ) : ℂ)");
        let expected_target = format!("Litex.In {rendered_power} Litex.Q");
        if rendered_target != expected_target {
            return Err("rational power rendering changed its verified target".into());
        }
        Ok(Some(format!(
            "Litex.Rules.complexRatInQ ({base} ^ {exponent})"
        )))
    }

    pub(super) fn construct_lean_binary_membership_from_conjunction_result(
        &mut self,
        target: &Fact,
        expected_set: StandardSet,
        theorem: &str,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(set) if *set == expected_set) {
            return Err(format!(
                "binary arithmetic membership target is not {expected_set}"
            ));
        }
        let (left, right) = match target_element {
            Obj::Add(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Sub(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Mul(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            Obj::Div(operation) => (operation.left.as_ref(), operation.right.as_ref()),
            _ => return Err("binary arithmetic membership changed its operator".into()),
        };
        let [conjunction_result] = subgoals else {
            return Err(
                "binary arithmetic membership requires one conjunction child Result".into(),
            );
        };
        let conjunction_result = conjunction_result
            .factual_success()
            .ok_or_else(|| "binary arithmetic conjunction child is not factual".to_string())?;
        if !conjunction_result.store.infers.is_empty() {
            return Err("binary arithmetic conjunction child published effects".into());
        }
        let components = conjunction_components(&conjunction_result.fact())?;
        let [left_component, right_component] = components.as_slice() else {
            return Err("binary arithmetic conjunction changed its component arity".into());
        };
        for (index, (component, expected_element)) in [left_component, right_component]
            .into_iter()
            .zip([left, right])
            .enumerate()
        {
            let (element, set) = membership_parts(component)?;
            if !matches!(set, Obj::StandardSet(actual) if *actual == expected_set)
                || obj_equality_key(element) != obj_equality_key(expected_element)
            {
                return Err(format!(
                    "binary arithmetic conjunction component {index} changed its operand"
                ));
            }
        }
        let Some(pair_proof) =
            self.construct_lean_proof_from_direct_fact_result(conjunction_result)?
        else {
            return Ok(None);
        };
        let pair_type = render_fact(&conjunction_result.fact(), &self.environment_stack)?;
        let left_proof =
            render_numeric_operand_membership(left, "__components.1", &self.environment_stack);
        let right_proof =
            render_numeric_operand_membership(right, "__components.2", &self.environment_stack);
        Ok(Some(format!(
            "(by\n  have __components : {pair_type} := {pair_proof}\n  exact Litex.Rules.{theorem} ({left_proof}) ({right_proof}))"
        )))
    }

    /// `Wrap` / `Combine`: replay the common sign and additive-order rules
    /// from their exact ordered child Results. Other arithmetic certificates
    /// remain fail-closed until their target representation and adapter have
    /// been reviewed.
    pub(super) fn construct_lean_arithmetic_builtin_from_result(
        &mut self,
        target: &Fact,
        rule: ArithmeticBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let sign_rule = match rule {
            ArithmeticBuiltinRule::AddNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::AddNonnegative)
            }
            ArithmeticBuiltinRule::AddPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositive)
            }
            ArithmeticBuiltinRule::AddPositiveLeftStrict => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict)
            }
            ArithmeticBuiltinRule::AddPositiveRightStrict => {
                Some(LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict)
            }
            ArithmeticBuiltinRule::MulNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::MulNonnegative)
            }
            ArithmeticBuiltinRule::MulPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::MulPositive)
            }
            ArithmeticBuiltinRule::DivNonnegative => {
                Some(LeanArithmeticBuiltinCompilationKind::DivNonnegative)
            }
            ArithmeticBuiltinRule::DivPositive => {
                Some(LeanArithmeticBuiltinCompilationKind::DivPositive)
            }
            _ => None,
        };
        let expected_child_count = match rule {
            _ if sign_rule.is_some() => 2,
            ArithmeticBuiltinRule::LessEqualFromStrictOrder
            | ArithmeticBuiltinRule::GreaterEqualFromStrictOrder
            | ArithmeticBuiltinRule::AddCommonLeftLessEqual
            | ArithmeticBuiltinRule::AddCommonLeftLess => 1,
            ArithmeticBuiltinRule::AddComponentwiseLessEqual
            | ArithmeticBuiltinRule::AddComponentwiseLess
            | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
            | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => 2,
            ArithmeticBuiltinRule::OrderTransitivity => {
                if subgoals.len() < 3 {
                    return Err(
                        "order transitivity lost its carrier evidence or ordered premises".into(),
                    );
                }
                subgoals.len()
            }
            _ => return Ok(None),
        };
        if subgoals.len() != expected_child_count {
            return Err(format!(
                "arithmetic rule {rule:?} changed its ordered child arity"
            ));
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("arithmetic child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("arithmetic child {index} published effects"));
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            children.push(CompiledFactProofBody {
                fact: child.fact(),
                proposition: String::new(),
                proof_expression,
            });
        }
        if let Some(sign_rule) = sign_rule {
            return Ok(Some(render_additive_sign_rule_from_compiled_children(
                target,
                sign_rule,
                &children,
                &self.environment_stack,
            )?));
        }

        if matches!(
            rule,
            ArithmeticBuiltinRule::AddCommonLeftLessEqual
                | ArithmeticBuiltinRule::AddCommonLeftLess
                | ArithmeticBuiltinRule::AddComponentwiseLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLess
                | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess
        ) {
            return Ok(Some(
                self.construct_lean_additive_order_rule_from_compiled_children(
                    target, rule, &children,
                )?,
            ));
        }

        if rule == ArithmeticBuiltinRule::OrderTransitivity {
            return Ok(Some(
                self.construct_lean_order_transitivity_from_compiled_children(target, &children)?,
            ));
        }

        let [source] = children.as_slice() else {
            unreachable!("strict-to-weak order rule retained one child")
        };
        let (target_left, target_right, target_is_strict) = order_relation_parts(target)?;
        let (source_left, source_right, source_is_strict) = order_relation_parts(&source.fact)?;
        if target_is_strict
            || !source_is_strict
            || obj_equality_key(target_left) != obj_equality_key(source_left)
            || obj_equality_key(target_right) != obj_equality_key(source_right)
        {
            return Err("strict-to-weak order rule changed its endpoints or orientation".into());
        }
        render_fact(target, &self.environment_stack)?;
        Ok(Some(if target_left.to_string() == "0" {
            format!("Litex.Positive.toNonnegative ({})", source.proof_expression)
        } else {
            format!("Litex.Lt.toLe ({})", source.proof_expression)
        }))
    }

    pub(super) fn construct_lean_additive_order_rule_from_compiled_children(
        &self,
        target: &Fact,
        rule: ArithmeticBuiltinRule,
        children: &[CompiledFactProofBody],
    ) -> Result<String, String> {
        let (target_left, target_right, target_is_strict) = order_relation_parts(target)?;
        let (target_left_common, target_left_addend) = addition_parts(target_left)?;
        let (target_right_common, target_right_addend) = addition_parts(target_right)?;

        let (expected_strictness, theorem): (Vec<bool>, &str) = match rule {
            ArithmeticBuiltinRule::AddCommonLeftLessEqual => {
                (vec![false], "complexAddPreservesLessEqualWithCommonLeft")
            }
            ArithmeticBuiltinRule::AddCommonLeftLess => {
                (vec![true], "complexAddPreservesLessWithCommonLeft")
            }
            ArithmeticBuiltinRule::AddComponentwiseLessEqual => (
                vec![false, false],
                "complexAddPreservesLessEqualComponentwise",
            ),
            ArithmeticBuiltinRule::AddComponentwiseLess => {
                (vec![true, true], "complexAddPreservesLessComponentwise")
            }
            ArithmeticBuiltinRule::AddComponentwiseLessLessEqual => (
                vec![true, false],
                "complexAddPreservesLessOfLessAndLessEqual",
            ),
            ArithmeticBuiltinRule::AddComponentwiseLessEqualLess => (
                vec![false, true],
                "complexAddPreservesLessOfLessEqualAndLess",
            ),
            _ => return Err(format!("unsupported additive order rule {rule:?}")),
        };
        let expected_target_strictness = expected_strictness.iter().any(|strict| *strict);
        if target_is_strict != expected_target_strictness
            || children.len() != expected_strictness.len()
        {
            return Err("additive order rule changed its target or premise arity".into());
        }

        if children.len() == 1 {
            if obj_equality_key(target_left_common) != obj_equality_key(target_right_common) {
                return Err("common-left additive order rule changed its common term".into());
            }
            let (premise_left, premise_right, premise_is_strict) =
                order_relation_parts(&children[0].fact)?;
            if premise_is_strict != expected_strictness[0]
                || obj_equality_key(premise_left) != obj_equality_key(target_left_addend)
                || obj_equality_key(premise_right) != obj_equality_key(target_right_addend)
            {
                return Err("common-left additive order rule changed its ordered premise".into());
            }
        } else {
            for (index, ((child, expected_is_strict), (expected_left, expected_right))) in children
                .iter()
                .zip(expected_strictness.iter())
                .zip([
                    (target_left_common, target_right_common),
                    (target_left_addend, target_right_addend),
                ])
                .enumerate()
            {
                let (premise_left, premise_right, premise_is_strict) =
                    order_relation_parts(&child.fact)?;
                if premise_is_strict != *expected_is_strict
                    || obj_equality_key(premise_left) != obj_equality_key(expected_left)
                    || obj_equality_key(premise_right) != obj_equality_key(expected_right)
                {
                    return Err(format!(
                        "componentwise additive order premise {index} changed its endpoints or strictness"
                    ));
                }
            }
        }

        render_fact(target, &self.environment_stack)?;
        let arguments = children
            .iter()
            .map(|child| format!("({})", child.proof_expression))
            .collect::<Vec<_>>()
            .join(" ");
        Ok(format!("Litex.Rules.{theorem} {arguments}"))
    }

    pub(super) fn construct_lean_order_transitivity_from_compiled_children(
        &self,
        target: &Fact,
        children: &[CompiledFactProofBody],
    ) -> Result<String, String> {
        if children.len() < 3 {
            return Err(
                "order transitivity requires carrier evidence followed by two premises".into(),
            );
        }
        let (carrier_evidence, ordered_premises) = children.split_at(children.len() - 2);
        let [first, second] = ordered_premises else {
            unreachable!("order transitivity retained two ordered premises")
        };
        for evidence in carrier_evidence {
            let components = match &evidence.fact {
                Fact::AndFact(_) | Fact::ChainFact(_) => conjunction_components(&evidence.fact)?,
                _ => vec![evidence.fact.clone()],
            };
            for component in components {
                let (_object, set) = membership_parts(&component)?;
                if !matches!(set, Obj::StandardSet(StandardSet::R | StandardSet::Z)) {
                    return Err(
                        "order transitivity carrier evidence changed from the verified R/Z fragment"
                            .into(),
                    );
                }
            }
        }

        let (target_left, target_right, target_strict) = order_relation_parts(target)?;
        let (first_left, middle, first_strict) = order_relation_parts(&first.fact)?;
        let (second_left, second_right, second_strict) = order_relation_parts(&second.fact)?;
        if obj_equality_key(target_left) != obj_equality_key(first_left)
            || obj_equality_key(middle) != obj_equality_key(second_left)
            || obj_equality_key(target_right) != obj_equality_key(second_right)
            || (target_strict && !first_strict && !second_strict)
        {
            return Err("order transitivity changed its ordered path".into());
        }
        if target_left.to_string() == "0"
            || first_left.to_string() == "0"
            || second_left.to_string() == "0"
        {
            return Err("mixed zero-ended order transitivity has no reviewed Lean adapter".into());
        }

        render_fact(target, &self.environment_stack)?;
        let first_proof = &first.proof_expression;
        let second_proof = &second.proof_expression;
        if target_strict {
            return Ok(match (first_strict, second_strict) {
                (true, true) => format!("Litex.Lt.trans ({first_proof}) ({second_proof})"),
                (true, false) => {
                    format!("Litex.Lt.transLe ({first_proof}) ({second_proof})")
                }
                (false, true) => {
                    format!("Litex.Le.transLt ({first_proof}) ({second_proof})")
                }
                (false, false) => unreachable!("strict target requires one strict premise"),
            });
        }
        let first_le = if first_strict {
            format!("Litex.Lt.toLe ({first_proof})")
        } else {
            format!("({first_proof})")
        };
        let second_le = if second_strict {
            format!("Litex.Lt.toLe ({second_proof})")
        } else {
            format!("({second_proof})")
        };
        Ok(format!("Litex.Le.trans {first_le} {second_le}"))
    }

    /// `Combine`: validate one registry-owned certificate directly from its
    /// stable rule identity, semantic fingerprint, matched bindings, and
    /// ordered child Results. This first direct tranche covers the complete
    /// registered set catalog; unsupported registered families remain on the
    /// compatibility path until their target renderers are migrated.
    pub(super) fn construct_lean_registered_local_builtin_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        self.validate_registered_local_builtin_target_and_child_arity(target, evidence, subgoals)?;
        let Some((set_rule, expected_binding_count, expected_semantic_premise_count)) =
            registered_set_rule(&evidence.rule_id, &evidence.semantic_fingerprint)
        else {
            return self
                .construct_lean_registered_arithmetic_rule_from_result(target, evidence, subgoals);
        };
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
        {
            return Err(format!(
                "registered set rule `{}` changed its binding or parameter-requirement arity",
                evidence.rule_id.as_str()
            ));
        }

        let mut semantic_premises = Vec::new();
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("registered set child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("registered set child {index} published effects"));
            }
            let fact = child.fact();
            let is_semantic_premise = if index >= evidence.parameter_requirement_count {
                true
            } else {
                let binding = &evidence.bindings[index];
                let (retained_binding, is_semantic_premise) = match &fact {
                    Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) => (&sethood.set, false),
                    Fact::AtomicFact(AtomicFact::InFact(membership)) => (&membership.element, true),
                    _ => {
                        return Err(format!(
                            "registered set parameter child {index} is neither sethood nor membership evidence"
                        ));
                    }
                };
                if !canonical_objs_equal(retained_binding, binding, MatchLimits::default())
                    .map_err(|error| error.message)?
                {
                    return Err(format!(
                        "registered set parameter child {index} changed its exact binding"
                    ));
                }
                is_semantic_premise
            };
            // A source `A set` parameter check is represented by the Lean
            // binder `A : Litex.Set`; it is a validated compiler input, not a
            // proposition that needs a separate Lean proof term.
            if !is_semantic_premise {
                continue;
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            semantic_premises.push(CompiledFactProofBody {
                proposition: String::new(),
                fact,
                proof_expression,
            });
        }
        if semantic_premises.len() != expected_semantic_premise_count {
            return Err(format!(
                "registered set rule `{}` changed its semantic premise count",
                evidence.rule_id.as_str()
            ));
        }

        let proof = match set_rule {
            LeanSetBuiltinCompilationKind::UnionCommutative
            | LeanSetBuiltinCompilationKind::UnionAssociative
            | LeanSetBuiltinCompilationKind::UnionIdempotent
            | LeanSetBuiltinCompilationKind::UnionEmptyIdentity
            | LeanSetBuiltinCompilationKind::IntersectCommutative
            | LeanSetBuiltinCompilationKind::IntersectAssociative => {
                if !semantic_premises.is_empty() {
                    return Err(
                        "registered structural set equality retained semantic premises".into(),
                    );
                }
                render_structural_set_equality(target, set_rule, &self.environment_stack)?
            }
            LeanSetBuiltinCompilationKind::UnionMembershipLeft
            | LeanSetBuiltinCompilationKind::UnionMembershipRight
            | LeanSetBuiltinCompilationKind::IntersectMembershipBoth
            | LeanSetBuiltinCompilationKind::SetMinusMembership => {
                let direct_rule = match set_rule {
                    LeanSetBuiltinCompilationKind::UnionMembershipLeft => {
                        SetBuiltinRule::UnionMembershipLeft
                    }
                    LeanSetBuiltinCompilationKind::UnionMembershipRight => {
                        SetBuiltinRule::UnionMembershipRight
                    }
                    LeanSetBuiltinCompilationKind::IntersectMembershipBoth => {
                        SetBuiltinRule::IntersectMembershipBoth
                    }
                    LeanSetBuiltinCompilationKind::SetMinusMembership => {
                        SetBuiltinRule::SetMinusMembership
                    }
                    _ => unreachable!("matched registered base set rule"),
                };
                let children = semantic_premises
                    .iter()
                    .map(|premise| (premise.fact.clone(), premise.proof_expression.clone()))
                    .collect::<Vec<_>>();
                render_base_set_builtin_rule_from_compiled_children(
                    target,
                    direct_rule,
                    &children,
                    &self.environment_stack,
                )?
            }
            _ => render_extended_set_rule(
                target,
                set_rule,
                &semantic_premises,
                &self.environment_stack,
            )?,
        };
        Ok(Some(proof))
    }

    /// `Combine`: registered arithmetic certificates retain real-parameter
    /// checks followed by the semantic premises in schema order. The stable
    /// RuleId selects one reviewed adapter only after the current registry
    /// fingerprint and every child shape have been validated.
    pub(super) fn construct_lean_registered_arithmetic_rule_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        #[derive(Clone, Copy)]
        enum RegisteredArithmeticRule {
            WeakOrderFromStrictOrder,
            SubtractionSign { strict: bool },
            Sign(LeanArithmeticBuiltinCompilationKind),
            AdditiveOrder(ArithmeticBuiltinRule),
        }

        let fingerprint = evidence.semantic_fingerprint.as_hex();
        let rule = match evidence.rule_id.as_str() {
            LESS_EQUAL_OF_LESS_RULE_ID if fingerprint == LESS_EQUAL_OF_LESS_FINGERPRINT => {
                RegisteredArithmeticRule::WeakOrderFromStrictOrder
            }
            "order.greater_equal_of_greater" => RegisteredArithmeticRule::WeakOrderFromStrictOrder,
            "order.sub_nonnegative_of_less_equal" => {
                RegisteredArithmeticRule::SubtractionSign { strict: false }
            }
            "order.sub_positive_of_less" => {
                RegisteredArithmeticRule::SubtractionSign { strict: true }
            }
            ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_RULE_ID
                if fingerprint == ADD_POSITIVE_OF_POSITIVE_NONNEGATIVE_FINGERPRINT =>
            {
                RegisteredArithmeticRule::Sign(
                    LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict,
                )
            }
            ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_RULE_ID
                if fingerprint == ADD_POSITIVE_OF_NONNEGATIVE_POSITIVE_FINGERPRINT =>
            {
                RegisteredArithmeticRule::Sign(
                    LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict,
                )
            }
            ADD_NONNEGATIVE_RULE_ID if fingerprint == ADD_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::AddNonnegative)
            }
            ADD_POSITIVE_RULE_ID if fingerprint == ADD_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::AddPositive)
            }
            MUL_NONNEGATIVE_RULE_ID if fingerprint == MUL_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::MulNonnegative)
            }
            MUL_POSITIVE_RULE_ID if fingerprint == MUL_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::MulPositive)
            }
            DIV_NONNEGATIVE_RULE_ID if fingerprint == DIV_NONNEGATIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::DivNonnegative)
            }
            DIV_POSITIVE_RULE_ID if fingerprint == DIV_POSITIVE_FINGERPRINT => {
                RegisteredArithmeticRule::Sign(LeanArithmeticBuiltinCompilationKind::DivPositive)
            }
            "order.add_le_add_left" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddCommonLeftLessEqual,
            ),
            "order.add_le_add" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqual,
            ),
            "order.add_lt_add_left" => {
                RegisteredArithmeticRule::AdditiveOrder(ArithmeticBuiltinRule::AddCommonLeftLess)
            }
            "order.add_lt_add" => {
                RegisteredArithmeticRule::AdditiveOrder(ArithmeticBuiltinRule::AddComponentwiseLess)
            }
            "order.add_lt_add_of_lt_of_le" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessLessEqual,
            ),
            "order.add_lt_add_of_le_of_lt" => RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqualLess,
            ),
            _ => return Ok(None),
        };
        let (expected_binding_count, expected_semantic_premise_count) = match rule {
            RegisteredArithmeticRule::WeakOrderFromStrictOrder
            | RegisteredArithmeticRule::SubtractionSign { .. } => (2, 1),
            RegisteredArithmeticRule::Sign(_) => (2, 2),
            RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddCommonLeftLessEqual
                | ArithmeticBuiltinRule::AddCommonLeftLess,
            ) => (3, 1),
            RegisteredArithmeticRule::AdditiveOrder(
                ArithmeticBuiltinRule::AddComponentwiseLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLess
                | ArithmeticBuiltinRule::AddComponentwiseLessLessEqual
                | ArithmeticBuiltinRule::AddComponentwiseLessEqualLess,
            ) => (4, 2),
            RegisteredArithmeticRule::AdditiveOrder(_) => {
                return Err("registered additive order rule has no reviewed arity".into());
            }
        };
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
            || subgoals.len() != expected_binding_count + expected_semantic_premise_count
        {
            return Err(format!(
                "registered arithmetic rule `{}` changed its certificate arity",
                evidence.rule_id.as_str()
            ));
        }

        let mut semantic_premises = Vec::with_capacity(expected_semantic_premise_count);
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("registered arithmetic child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!(
                    "registered arithmetic child {index} published effects"
                ));
            }
            let Some(proof_expression) =
                self.construct_lean_proof_from_direct_fact_result(child)?
            else {
                return Ok(None);
            };
            let fact = child.fact();
            if index < evidence.parameter_requirement_count {
                let (element, set) = membership_parts(&fact)?;
                if !matches!(set, Obj::StandardSet(StandardSet::R))
                    || !canonical_objs_equal(
                        element,
                        &evidence.bindings[index],
                        MatchLimits::default(),
                    )
                    .map_err(|error| error.message)?
                {
                    return Err(format!(
                        "registered arithmetic parameter child {index} changed its exact real binding"
                    ));
                }
                continue;
            }
            semantic_premises.push(CompiledFactProofBody {
                fact,
                proposition: String::new(),
                proof_expression,
            });
        }

        let proof = match rule {
            RegisteredArithmeticRule::Sign(rule) => {
                render_additive_sign_rule_from_compiled_children(
                    target,
                    rule,
                    &semantic_premises,
                    &self.environment_stack,
                )?
            }
            RegisteredArithmeticRule::AdditiveOrder(rule) => self
                .construct_lean_additive_order_rule_from_compiled_children(
                    target,
                    rule,
                    &semantic_premises,
                )?,
            RegisteredArithmeticRule::WeakOrderFromStrictOrder => {
                let [premise] = semantic_premises.as_slice() else {
                    unreachable!("registered less-equal rule retained one premise")
                };
                let (strict_left, strict_right, premise_is_strict) =
                    order_relation_parts(&premise.fact)?;
                let (weak_left, weak_right, target_is_strict) = order_relation_parts(target)?;
                if !premise_is_strict
                    || target_is_strict
                    || obj_equality_key(strict_left) != obj_equality_key(weak_left)
                    || obj_equality_key(strict_right) != obj_equality_key(weak_right)
                {
                    return Err(
                        "registered strict-to-weak order rule changed its relation or ordered endpoints"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                if strict_left.to_string() == "0" {
                    format!(
                        "Litex.Positive.toNonnegative ({})",
                        premise.proof_expression
                    )
                } else {
                    format!("Litex.Lt.toLe ({})", premise.proof_expression)
                }
            }
            RegisteredArithmeticRule::SubtractionSign { strict } => {
                let [premise] = semantic_premises.as_slice() else {
                    unreachable!("registered subtraction-sign rule retained one premise")
                };
                let (premise_left, premise_right, premise_is_strict) =
                    order_relation_parts(&premise.fact)?;
                let (target_zero, target_expression) = positive_order_parts(target, strict)?;
                let Obj::Sub(subtraction) = target_expression else {
                    return Err(
                        "registered subtraction-sign rule changed its target operator".into(),
                    );
                };
                if premise_is_strict != strict
                    || target_zero.to_string() != "0"
                    || obj_equality_key(premise_left)
                        != obj_equality_key(subtraction.right.as_ref())
                    || obj_equality_key(premise_right)
                        != obj_equality_key(subtraction.left.as_ref())
                {
                    return Err(
                        "registered subtraction-sign rule changed its ordered operands or strictness"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                let theorem = if strict {
                    "complexSubPositiveOfLess"
                } else {
                    "complexSubNonnegativeOfLessEqual"
                };
                format!("Litex.Rules.{theorem} ({})", premise.proof_expression)
            }
        };
        Ok(Some(proof))
    }

    pub(super) fn validate_registered_local_builtin_target_and_child_arity(
        &self,
        target: &Fact,
        evidence: &RegisteredLocalBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<(), String> {
        let registered_fingerprint = registered_local_builtin_fingerprint_by_id(&evidence.rule_id)
            .map_err(|error| {
                format!("failed to read registered local builtin metadata: {error:?}")
            })?
            .ok_or_else(|| {
                format!(
                    "unknown local builtin RuleId `{}`",
                    evidence.rule_id.as_str()
                )
            })?;
        if registered_fingerprint != evidence.semantic_fingerprint {
            return Err(format!(
                "stale local builtin fingerprint for `{}`",
                evidence.rule_id.as_str()
            ));
        }
        let Some((set_rule, expected_binding_count, expected_semantic_premise_count)) =
            registered_set_rule(&evidence.rule_id, &evidence.semantic_fingerprint)
        else {
            return Ok(());
        };
        if !matches!(target, Fact::AtomicFact(_)) {
            return Err("local builtin certificate target must be atomic".into());
        }
        if evidence.bindings.len() != expected_binding_count
            || evidence.parameter_requirement_count != expected_binding_count
        {
            return Err(
                "local builtin certificate has the wrong binding or requirement arity".into(),
            );
        }
        let membership_parameter_count = usize::from(matches!(
            set_rule,
            LeanSetBuiltinCompilationKind::UnionMembershipLeft
                | LeanSetBuiltinCompilationKind::UnionMembershipRight
                | LeanSetBuiltinCompilationKind::IntersectMembershipBoth
                | LeanSetBuiltinCompilationKind::SetMinusMembership
        ));
        let expected_child_count =
            expected_binding_count + expected_semantic_premise_count - membership_parameter_count;
        if subgoals.len() != expected_child_count {
            return Err("local builtin certificate has the wrong child-proof arity".into());
        }
        Ok(())
    }

    pub(super) fn construct_lean_set_builtin_from_result(
        &mut self,
        target: &Fact,
        rule: SetBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if matches!(
            rule,
            SetBuiltinRule::SubsetReflexivity | SetBuiltinRule::SupersetReflexivity
        ) {
            if !subgoals.is_empty() {
                return Err("set-relation reflexivity unexpectedly gained child Results".into());
            }
            return Ok(Some(render_set_relation_reflexivity(
                target,
                rule == SetBuiltinRule::SubsetReflexivity,
                &self.environment_stack,
            )?));
        }
        if matches!(
            rule,
            SetBuiltinRule::UnionCommutative
                | SetBuiltinRule::UnionAssociative
                | SetBuiltinRule::UnionIdempotent
                | SetBuiltinRule::UnionEmptyIdentity
                | SetBuiltinRule::IntersectCommutative
                | SetBuiltinRule::IntersectAssociative
        ) {
            if !subgoals.is_empty() {
                return Err("structural set equality unexpectedly gained child Results".into());
            }
            let compatibility_rule = match rule {
                SetBuiltinRule::UnionCommutative => LeanSetBuiltinCompilationKind::UnionCommutative,
                SetBuiltinRule::UnionAssociative => LeanSetBuiltinCompilationKind::UnionAssociative,
                SetBuiltinRule::UnionIdempotent => LeanSetBuiltinCompilationKind::UnionIdempotent,
                SetBuiltinRule::UnionEmptyIdentity => {
                    LeanSetBuiltinCompilationKind::UnionEmptyIdentity
                }
                SetBuiltinRule::IntersectCommutative => {
                    LeanSetBuiltinCompilationKind::IntersectCommutative
                }
                SetBuiltinRule::IntersectAssociative => {
                    LeanSetBuiltinCompilationKind::IntersectAssociative
                }
                _ => unreachable!("matched structural set rule"),
            };
            return Ok(Some(render_structural_set_equality(
                target,
                compatibility_rule,
                &self.environment_stack,
            )?));
        }
        let mut children = Vec::with_capacity(subgoals.len());
        for (index, child) in subgoals.iter().enumerate() {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("set builtin child {index} is not factual"))?;
            if !child.store.infers.is_empty() {
                return Err(format!("set builtin child {index} published effects"));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            children.push((child.fact(), proof));
        }
        Ok(Some(render_base_set_builtin_rule_from_compiled_children(
            target,
            rule,
            &children,
            &self.environment_stack,
        )?))
    }

    /// `Reuse` / `Combine`: every edge cites the exact previously stored
    /// equality FactId retained by the verifier. No proposition lookup or
    /// equality-graph search is repeated in the compiler.
    pub(super) fn construct_lean_known_equality_path_from_result(
        &self,
        target: &Fact,
        evidence: &KnownEqualityBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<String, String> {
        if evidence.expected_target.to_string() != target.to_string() || !subgoals.is_empty() {
            return Err("known-equality path changed its target or gained child Results".into());
        }
        let (target_left, target_right) = equality_parts(target)?;
        if evidence.steps.is_empty() {
            return Err("known-equality path retained no steps".into());
        }
        let mut current_key = obj_equality_key(target_left);
        let target_key = obj_equality_key(target_right);
        let mut accumulated: Option<String> = None;
        for (index, step) in evidence.steps.iter().enumerate() {
            if current_key != obj_equality_key(&step.from) {
                return Err(format!("known-equality path step {index} is disconnected"));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let reverse = if from_key == left_key && to_key == right_key {
                false
            } else if from_key == right_key && to_key == left_key {
                true
            } else {
                return Err(format!(
                    "known-equality path step {index} has invalid orientation"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let cited = resolve_fact_citation(
                &step.source_fact_id,
                &equality_fact,
                &self.environment_stack,
            )?;
            let oriented = if reverse {
                format!("Litex.Same.symm ({cited})")
            } else {
                cited
            };
            accumulated = Some(match accumulated {
                None => oriented,
                Some(previous) => format!("Litex.Same.trans ({previous}) ({oriented})"),
            });
            current_key = to_key;
        }
        if current_key != target_key {
            return Err("known-equality path does not end at its target".into());
        }
        render_fact(target, &self.environment_stack)?;
        accumulated.ok_or_else(|| "known-equality path retained no proof".into())
    }

    /// `PassThrough`: subset/superset dual spellings lower to the same Lean
    /// proposition. The one exact child Result therefore supplies the proof,
    /// while the typed rule fixes which source-level conversion occurred.
    pub(super) fn construct_lean_set_relation_duality_from_result(
        &mut self,
        target: &Fact,
        rule: SetRelationDualityBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [child] = subgoals else {
            return Err("set-relation duality requires one child Result".into());
        };
        let child = child
            .factual_success()
            .ok_or_else(|| "set-relation duality child is not factual".to_string())?;
        if !child.store.infers.is_empty() {
            return Err("set-relation duality child published effects".into());
        }
        let (target_left, target_right, target_negated, target_is_subset_spelling) =
            normalized_set_relation_parts(target)?;
        let child_fact = child.fact();
        let (child_left, child_right, child_negated, child_is_subset_spelling) =
            normalized_set_relation_parts(&child_fact)?;
        let expected_target_subset_spelling = match rule {
            SetRelationDualityBuiltinRule::SubsetFromSuperset
            | SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset => true,
            SetRelationDualityBuiltinRule::SupersetFromSubset
            | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset => false,
        };
        let expected_negated = matches!(
            rule,
            SetRelationDualityBuiltinRule::NotSubsetFromNotSuperset
                | SetRelationDualityBuiltinRule::NotSupersetFromNotSubset
        );
        if target_is_subset_spelling != expected_target_subset_spelling
            || child_is_subset_spelling == target_is_subset_spelling
            || target_negated != expected_negated
            || child_negated != expected_negated
            || obj_equality_key(target_left) != obj_equality_key(child_left)
            || obj_equality_key(target_right) != obj_equality_key(child_right)
        {
            return Err("set-relation duality changed its orientation or endpoints".into());
        }
        if render_fact(target, &self.environment_stack)?
            != render_fact(&child_fact, &self.environment_stack)?
        {
            return Err("set-relation duality no longer lowers to one Lean proposition".into());
        }
        self.construct_lean_proof_from_direct_fact_result(child)
    }

    /// `Wrap`: cite the exact source FactId, then apply the verifier-retained
    /// equality edges in their recorded order. The Result owns both the
    /// orientation and the equality FactId of every edge; the compiler does
    /// not search the current environment for a proposition-shaped match.
    pub(super) fn construct_lean_fact_citation_with_equality_transport_from_result(
        &self,
        target: &Fact,
        cited_statement: &Stmt,
        source_fact_id: Option<FactId>,
        equality_transport: Option<&EqualityTransportEvidence>,
    ) -> Result<Option<String>, String> {
        let Stmt::Fact(source_fact) = cited_statement else {
            return Ok(None);
        };
        let Some(source_fact_id) = source_fact_id else {
            return Ok(None);
        };
        let mut proof =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        if equality_transport_has_no_steps(equality_transport) {
            if facts_are_comparison_notation_duals(source_fact, target)
                && render_fact(source_fact, &self.environment_stack)?
                    == render_fact(target, &self.environment_stack)?
            {
                return Ok(Some(proof));
            }
            return Ok(Some(resolve_fact_citation(
                &source_fact_id,
                target,
                &self.environment_stack,
            )?));
        }

        let (source_element, source_set) = membership_parts(source_fact)?;
        let mut current_element = source_element.clone();
        let (target_element, target_set) = membership_parts(target)?;
        if obj_equality_key(source_set) != obj_equality_key(target_set) {
            return Err("equality transport changed the membership set".into());
        }
        let rendered_set = render_obj(target_set, &self.environment_stack)?;
        for (step_index, step) in equality_transport
            .expect("nonempty transport checked above")
            .steps
            .iter()
            .enumerate()
        {
            if obj_equality_key(&current_element) != obj_equality_key(&step.from) {
                return Err(format!(
                    "equality transport step {step_index} does not start at the current membership element"
                ));
            }
            let left_key = obj_equality_key(&step.equality.left);
            let right_key = obj_equality_key(&step.equality.right);
            let from_key = obj_equality_key(&step.from);
            let to_key = obj_equality_key(&step.to);
            let direction = if from_key == left_key && to_key == right_key {
                "mp"
            } else if from_key == right_key && to_key == left_key {
                "mpr"
            } else {
                return Err(format!(
                    "equality transport step {step_index} is not oriented by its retained equality"
                ));
            };
            let equality_fact: Fact = AtomicFact::EqualFact(step.equality.clone()).into();
            let equality_fact_id = step.equality_fact_id;
            let equality_proof =
                resolve_fact_citation(&equality_fact_id, &equality_fact, &self.environment_stack)?;
            proof =
                format!("(Litex.In.congr ({equality_proof}) {rendered_set}).{direction} ({proof})");
            current_element = step.to.clone();
        }
        if obj_equality_key(&current_element) != obj_equality_key(target_element) {
            return Err("equality transport did not end at the target membership element".into());
        }
        Ok(Some(proof))
    }

    pub(super) fn construct_lean_stored_fact_citation_proof_from_result(
        &self,
        target: &Fact,
        citation: &SuccessStoredFactCitationProofResult,
    ) -> Result<Option<String>, String> {
        self.construct_lean_fact_citation_with_equality_transport_from_result(
            target,
            &citation.source_fact.clone().into_stmt(),
            Some(citation.source_fact_id),
            None,
        )
    }

    /// `Leaf`: replay the verifier-selected one-step unfolding of a checked
    /// named function. The defining equality is resolved by exact `FactId`;
    /// the application orientation and reduced body come from the Result.
    pub(super) fn construct_lean_checked_function_definition_reduction_from_result(
        &self,
        target: &Fact,
        reduction: &CheckedFunctionDefinitionReductionEvidence,
    ) -> Result<String, String> {
        let (target_left, target_right) = equality_parts(target)?;
        let (expected_application, expected_other) = if reduction.application_is_left {
            (target_left, target_right)
        } else {
            (target_right, target_left)
        };
        if obj_equality_key(expected_application) != obj_equality_key(&reduction.application_side)
            || obj_equality_key(expected_other) != obj_equality_key(&reduction.other_side)
        {
            return Err(
                "checked function-definition reduction changed its goal orientation".into(),
            );
        }
        if !reduction.reduced_matches_other_by_alpha
            || !objs_equal_with_nested_binder_alpha_equivalence(
                &reduction.reduced,
                &reduction.other_side,
            )
        {
            return Err("checked function-definition reduction changed its reduced result".into());
        }
        let Fact::AtomicFact(AtomicFact::EqualFact(defining_equality)) =
            &reduction.defining_equality
        else {
            return Err("checked function-definition source is not an equality".into());
        };
        if obj_equality_key(&defining_equality.left)
            != obj_equality_key(&reduction.definition_object)
            || !matches!(&defining_equality.right, Obj::AnonymousFn(_))
        {
            return Err(
                "checked function-definition source changed its named-function definition".into(),
            );
        }
        resolve_fact_citation(
            &reduction.defining_equality_fact_id,
            &reduction.defining_equality,
            &self.environment_stack,
        )?;
        let binding = self
            .environment_stack
            .named_function_definitions
            .get(&reduction.defining_equality_fact_id)
            .ok_or_else(|| {
                format!(
                    "checked function-definition reduction references unavailable defining FactId `{}`",
                    reduction.defining_equality_fact_id
                )
            })?;
        if !object_is_symbol(&reduction.definition_object, binding.symbol_id) {
            return Err(
                "checked function-definition reduction changed its named function symbol".into(),
            );
        }
        let application_side = if reduction.application_is_left {
            LeanEqualityApplicationSide::Left
        } else {
            LeanEqualityApplicationSide::Right
        };
        render_checked_identity_function_reduction_from_fact(
            target,
            reduction.defining_equality_fact_id,
            application_side,
            &self.environment_stack,
        )
    }

    pub(super) fn construct_lean_single_fact_transformation_from_result(
        &mut self,
        target: &Fact,
        transformation: &SuccessTransformFactResult,
    ) -> Result<Option<String>, String> {
        let source = transformation.source.fact();
        let Some(source_proof) = self
            .construct_lean_proof_from_shared_verify_fact_result(transformation.source.as_ref())?
        else {
            return Ok(None);
        };
        Ok(Some(
            self.construct_lean_fact_transformation_step_from_result(
                &source,
                target,
                source_proof,
                &transformation.rule,
                0,
            )?,
        ))
    }

    pub(super) fn construct_lean_fact_transformation_step_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        source_proof: String,
        rule: &FactTransformationRule,
        step_index: usize,
    ) -> Result<String, String> {
        match rule {
            FactTransformationRule::RationalNormalization => {
                if !facts_align_by_nested_rational_normalization_for_result_compiler(source, target)
                {
                    return Err(format!(
                        "fact transformation step {step_index} does not retain a rational-normalization shape"
                    ));
                }
                render_fact(source, &self.environment_stack)?;
                render_fact(target, &self.environment_stack)?;
                Ok(format!(
                    "(by\n  convert {source_proof} using 1 <;> norm_num)"
                ))
            }
            FactTransformationRule::EqualityRewrite(evidence) => self
                .construct_lean_equality_rewrite_transformation_from_result(
                    source,
                    target,
                    source_proof,
                    evidence,
                    step_index,
                ),
        }
    }

    pub(super) fn construct_lean_equality_rewrite_transformation_from_result(
        &self,
        source: &Fact,
        target: &Fact,
        mut proof: String,
        evidence: &EqualityTransportEvidence,
        transformation_step_index: usize,
    ) -> Result<String, String> {
        if evidence.steps.is_empty() {
            return if source.to_string() == target.to_string() {
                Ok(proof)
            } else {
                Err(format!(
                    "fact transformation step {transformation_step_index} has an empty equality rewrite"
                ))
            };
        }

        match (source, target) {
            (
                Fact::AtomicFact(AtomicFact::InFact(source_membership)),
                Fact::AtomicFact(AtomicFact::InFact(target_membership)),
            ) => {
                if obj_equality_key(&source_membership.set)
                    != obj_equality_key(&target_membership.set)
                {
                    return Err("fact transformation equality rewrite changed its set".into());
                }
                let rendered_set = render_obj(&target_membership.set, &self.environment_stack)?;
                let mut current = source_membership.element.clone();
                for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
                    if obj_equality_key(&current) != obj_equality_key(&rewrite.from) {
                        return Err(format!(
                            "fact transformation equality rewrite {rewrite_index} does not start at the current member"
                        ));
                    }
                    let (equality_proof, forward) =
                        self.resolve_equality_rewrite_proof(rewrite, rewrite_index)?;
                    let direction = if forward { "mp" } else { "mpr" };
                    proof = format!(
                        "(Litex.In.congr ({equality_proof}) {rendered_set}).{direction} ({proof})"
                    );
                    current = rewrite.to.clone();
                }
                if obj_equality_key(&current) != obj_equality_key(&target_membership.element) {
                    return Err(
                        "fact transformation equality rewrite did not reach its target member"
                            .into(),
                    );
                }
                Ok(proof)
            }
            (
                Fact::AtomicFact(AtomicFact::EqualFact(source_equality)),
                Fact::AtomicFact(AtomicFact::EqualFact(target_equality)),
            ) => {
                let mut current_left = source_equality.left.clone();
                let mut current_right = source_equality.right.clone();
                for (rewrite_index, rewrite) in evidence.steps.iter().enumerate() {
                    let rewrites_left =
                        obj_equality_key(&current_left) == obj_equality_key(&rewrite.from);
                    let rewrites_right =
                        obj_equality_key(&current_right) == obj_equality_key(&rewrite.from);
                    if rewrites_left == rewrites_right {
                        return Err(format!(
                            "fact transformation equality rewrite {rewrite_index} does not select exactly one equality endpoint"
                        ));
                    }
                    let (equality_proof, forward) =
                        self.resolve_equality_rewrite_proof(rewrite, rewrite_index)?;
                    let oriented_equality_proof = if forward {
                        equality_proof
                    } else {
                        format!("Litex.Same.symm ({equality_proof})")
                    };
                    if rewrites_left {
                        proof = format!(
                            "Litex.Same.trans (Litex.Same.symm ({oriented_equality_proof})) ({proof})"
                        );
                        current_left = rewrite.to.clone();
                    } else {
                        proof = format!("Litex.Same.trans ({proof}) ({oriented_equality_proof})");
                        current_right = rewrite.to.clone();
                    }
                }
                if obj_equality_key(&current_left) != obj_equality_key(&target_equality.left)
                    || obj_equality_key(&current_right) != obj_equality_key(&target_equality.right)
                {
                    return Err(
                        "fact transformation equality rewrite did not reach its target equality"
                            .into(),
                    );
                }
                render_fact(target, &self.environment_stack)?;
                Ok(proof)
            }
            _ => Err(format!(
                "fact transformation equality rewrite does not support `{source}` -> `{target}`"
            )),
        }
    }

    pub(super) fn resolve_equality_rewrite_proof(
        &self,
        rewrite: &EqualityTransportStep,
        rewrite_index: usize,
    ) -> Result<(String, bool), String> {
        let equality_fact: Fact = AtomicFact::EqualFact(rewrite.equality.clone()).into();
        let fact_id = rewrite.equality_fact_id;
        let proof = resolve_fact_citation(&fact_id, &equality_fact, &self.environment_stack)?;
        let left = obj_equality_key(&rewrite.equality.left);
        let right = obj_equality_key(&rewrite.equality.right);
        let from = obj_equality_key(&rewrite.from);
        let to = obj_equality_key(&rewrite.to);
        if from == left && to == right {
            Ok((proof, true))
        } else if from == right && to == left {
            Ok((proof, false))
        } else {
            Err(format!(
                "fact transformation equality rewrite {rewrite_index} is not oriented by its retained equality"
            ))
        }
    }

    /// `Wrap`: compile the one exact source-membership child first and then
    /// apply the fixed standard-set inclusion chain selected by the retained
    /// source and target sets. This consumes the recursive Result directly;
    /// no diagnostic label or compatibility proof IR participates.
    pub(super) fn construct_lean_standard_set_membership_projection_from_result(
        &mut self,
        target: &Fact,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let [source_result] = subgoals else {
            return Err(
                "standard-set membership projection requires exactly one child Result".into(),
            );
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "standard-set membership projection child is not factual".to_string())?;
        let source = source_result.fact();
        if source_result.store.fact.to_string() != source.to_string()
            || !source_result.store.infers.is_empty()
        {
            return Err(
                "standard-set membership projection child changed its fact or published effects"
                    .into(),
            );
        }
        let (target_element, target_set) = membership_parts(target)?;
        let (source_element, source_set) = membership_parts(&source)?;
        if obj_equality_key(target_element) != obj_equality_key(source_element) {
            return Err("standard-set membership projection changed its source element".into());
        }
        let (Obj::StandardSet(source_set), Obj::StandardSet(target_set)) = (source_set, target_set)
        else {
            return Err("standard-set membership projection retained a nonstandard set".into());
        };
        let Some(mut proof) = self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        for theorem in standard_set_membership_projection_theorem_chain(*source_set, *target_set)? {
            proof = format!("Litex.Rules.{theorem} ({proof})");
        }
        Ok(Some(proof))
    }

    /// `Combine`: resolve the retained source forall by its exact FactId,
    /// compile each parameter/domain requirement from its recursive Result,
    /// and apply the already-emitted Lean theorem. The fresh Runtime below is
    /// used only as the kernel's stateless syntax-substitution utility; it has
    /// no executed environment and cannot rediscover a proof or FactId.
    pub(super) fn construct_lean_known_forall_instantiation_from_result(
        &mut self,
        target: &Fact,
        result: &SuccessInstantiateKnownForallResult,
    ) -> Result<Option<String>, String> {
        let source_fact = &result.source_fact;
        let Fact::ForallFact(source_forall) = source_fact else {
            return Err("known-forall Result cited a non-forall fact".into());
        };
        let source_fact_id = result.source_fact_id;
        let source_theorem =
            resolve_fact_citation(&source_fact_id, source_fact, &self.environment_stack)?;
        let source_parameters = source_forall
            .params_def_with_type
            .collect_param_bindings_with_types();
        if source_parameters.len() != result.instantiation.len() {
            return Err("known-forall Result changed its argument arity".into());
        }
        if result.requirements.len() != source_parameters.len() + source_forall.dom_facts.len() {
            return Err(
                "known-forall Result changed its parameter/domain requirement arity".into(),
            );
        }

        let arguments = result
            .instantiation
            .iter()
            .zip(source_parameters.iter())
            .map(|(item, (binding, _))| {
                if item.param != binding.name() || item.arg != item.arg_obj.to_string() {
                    return Err(
                        "known-forall Result changed its retained parameter order or argument"
                            .to_string(),
                    );
                }
                Ok(item.arg_obj.clone())
            })
            .collect::<Result<Vec<_>, String>>()?;
        let substitutions = source_forall
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(&arguments);
        let substitution_runtime = Runtime::new();

        let mut application_terms = vec![source_theorem];
        for (parameter_index, (((_, parameter_type), argument), requirement)) in source_parameters
            .iter()
            .zip(arguments.iter())
            .zip(result.requirements.iter().take(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::ParameterType {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its kind"
                ));
            }
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall parameter requirement {parameter_index} is not factual")
            })?;
            if requirement_result.fact().to_string() != requirement.stmt.to_string()
                || requirement_result.store.fact.to_string() != requirement.stmt.to_string()
                || requirement_result.store.fact_id.is_some()
                || !requirement_result.store.infers.is_empty()
            {
                return Err(format!(
                    "known-forall parameter requirement {parameter_index} changed its fact or published effects"
                ));
            }

            application_terms.push(render_obj(argument, &self.environment_stack)?);
            let requirement_needs_proof = match parameter_type {
                ParamType::Set(_) => {
                    let Fact::AtomicFact(AtomicFact::IsSetFact(sethood)) = &requirement.stmt else {
                        return Err(
                            "known-forall set argument retained a non-set requirement".into()
                        );
                    };
                    if obj_equality_key(&sethood.set) != obj_equality_key(argument) {
                        return Err("known-forall set requirement changed its argument".into());
                    }
                    false
                }
                ParamType::Obj(source_set) => {
                    let instantiated_set = substitution_runtime
                        .inst_obj(source_set, &substitutions, ParamObjType::Forall)
                        .map_err(|error| {
                            format!("known-forall parameter substitution failed: {error:?}")
                        })?;
                    let (requirement_argument, requirement_set) =
                        membership_parts(&requirement.stmt)?;
                    if obj_equality_key(requirement_argument) != obj_equality_key(argument)
                        || obj_equality_key(requirement_set) != obj_equality_key(&instantiated_set)
                    {
                        return Err(
                            "known-forall object requirement changed its argument or carrier"
                                .into(),
                        );
                    }
                    true
                }
                ParamType::NonemptySet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(property)) =
                        &requirement.stmt
                    else {
                        return Err(
                            "known-forall nonempty-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall nonempty-set requirement changed its argument".into()
                        );
                    }
                    true
                }
                ParamType::FiniteSet(_) => {
                    let Fact::AtomicFact(AtomicFact::IsFiniteSetFact(property)) = &requirement.stmt
                    else {
                        return Err(
                            "known-forall finite-set argument retained different evidence".into(),
                        );
                    };
                    if obj_equality_key(&property.set) != obj_equality_key(argument) {
                        return Err(
                            "known-forall finite-set requirement changed its argument".into()
                        );
                    }
                    true
                }
            };
            if requirement_needs_proof {
                let Some(proof) =
                    self.construct_lean_proof_from_direct_fact_result(requirement_result)?
                else {
                    return Ok(None);
                };
                application_terms.push(format!("({proof})"));
            }
        }

        for (domain_index, (source_domain, requirement)) in source_forall
            .dom_facts
            .iter()
            .zip(result.requirements.iter().skip(source_parameters.len()))
            .enumerate()
        {
            if requirement.kind != KnownForallRequirementKind::Domain {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its kind"
                ));
            }
            let expected_domain = substitution_runtime
                .inst_fact(source_domain, &substitutions, ParamObjType::Forall, None)
                .map_err(|error| format!("known-forall domain substitution failed: {error:?}"))?;
            let requirement_result = requirement.result.factual_success().ok_or_else(|| {
                format!("known-forall domain requirement {domain_index} is not factual")
            })?;
            if requirement.stmt.to_string() != expected_domain.to_string()
                || requirement_result.fact().to_string() != expected_domain.to_string()
                || requirement_result.store.fact.to_string() != expected_domain.to_string()
                || requirement_result.store.fact_id.is_some()
                || !requirement_result.store.infers.is_empty()
            {
                return Err(format!(
                    "known-forall domain requirement {domain_index} changed its instantiated fact or published effects"
                ));
            }
            let Some(proof) =
                self.construct_lean_proof_from_direct_fact_result(requirement_result)?
            else {
                return Ok(None);
            };
            application_terms.push(format!("({proof})"));
        }

        let [source_conclusion] = source_forall.then_facts.as_slice() else {
            return Ok(None);
        };
        let instantiated_conclusion = substitution_runtime
            .inst_fact(
                &source_conclusion.clone().to_fact(),
                &substitutions,
                ParamObjType::Forall,
                None,
            )
            .map_err(|error| format!("known-forall conclusion substitution failed: {error:?}"))?;
        let application = format!("({})", application_terms.join(" "));
        if instantiated_conclusion.to_string() == target.to_string() {
            return Ok(Some(application));
        }
        if facts_align_by_nested_rational_normalization_for_result_compiler(
            &instantiated_conclusion,
            target,
        ) {
            render_fact(target, &self.environment_stack)?;
            return Ok(Some(format!(
                "(by\n  convert {application} using 1 <;> norm_num)"
            )));
        }
        Err(format!(
            "known-forall instance `{instantiated_conclusion}` does not match target `{target}`"
        ))
    }

    /// `Wrap`: the arithmetic-closure Result owns exactly one conjunction
    /// child Result. The child retains the two ordered operand memberships;
    /// no diagnostic label or rebuilt verifier search participates here.
    pub(super) fn construct_lean_real_arithmetic_membership_closure_from_result(
        &mut self,
        target: &Fact,
        rule: RealArithmeticMembershipClosureBuiltinRule,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let (target_element, target_set) = membership_parts(target)?;
        if !matches!(target_set, Obj::StandardSet(StandardSet::R)) {
            return Err("real arithmetic membership Result changed its target carrier".into());
        }
        let (left, right, theorem) = match (rule, target_element) {
            (RealArithmeticMembershipClosureBuiltinRule::Add, Obj::Add(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexAddInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Sub, Obj::Sub(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexSubInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Mul, Obj::Mul(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexMulInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Div, Obj::Div(operation)) => (
                operation.left.as_ref(),
                operation.right.as_ref(),
                "complexDivInR",
            ),
            (RealArithmeticMembershipClosureBuiltinRule::Pow, _) => return Ok(None),
            _ => {
                return Err("real arithmetic membership Result changed its source operator".into());
            }
        };
        let [components] = subgoals else {
            return Err(
                "real arithmetic membership Result must retain one conjunction child".into(),
            );
        };
        let components = components
            .factual_success()
            .ok_or_else(|| "real arithmetic membership child is not factual".to_string())?;
        if !components.store.infers.is_empty() || components.store.fact_id.is_some() {
            return Err(
                "real arithmetic membership conjunction child unexpectedly published effects"
                    .into(),
            );
        }
        let retained_components = conjunction_components(&components.fact())?;
        if retained_components.len() != 2 {
            return Err("real arithmetic membership child is not a binary conjunction".into());
        }
        for (retained, expected_operand) in
            retained_components.iter().zip([left, right].into_iter())
        {
            let (retained_element, retained_set) = membership_parts(retained)?;
            if !matches!(retained_set, Obj::StandardSet(StandardSet::R))
                || obj_equality_key(retained_element) != obj_equality_key(expected_operand)
            {
                return Err("real arithmetic membership child changed its ordered operands".into());
            }
        }
        let components_proof = self
            .construct_lean_proof_from_direct_fact_result(components)?
            .ok_or_else(|| {
                "real arithmetic membership conjunction has no direct recursive Result proof adapter"
                    .to_string()
            })?;
        let components_type = render_fact(&components.fact(), &self.environment_stack)?;
        let left_proof =
            render_real_operand_membership(left, "__components.1", &self.environment_stack);
        let right_proof =
            render_real_operand_membership(right, "__components.2", &self.environment_stack);
        Ok(Some(format!(
            "(by\n  have __components : {components_type} := {components_proof}\n  exact Litex.Rules.{theorem} ({left_proof}) ({right_proof}))"
        )))
    }

    pub(super) fn construct_lean_disjunction_introduction_from_result(
        &mut self,
        target: &Fact,
        evidence: &DisjunctionIntroductionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("disjunction-introduction evidence changed its target".into());
        }
        let branches = disjunction_components(target)?;
        let Some(selected) = branches.get(evidence.selected_index) else {
            return Err("disjunction-introduction evidence selected no target branch".into());
        };
        if selected.to_string() != evidence.expected_selected.to_string() {
            return Err("disjunction-introduction evidence changed its selected branch".into());
        }
        let [selected_result] = subgoals else {
            return Err(
                "disjunction-introduction evidence must retain one selected child Result".into(),
            );
        };
        let selected_result = selected_result
            .factual_success()
            .ok_or_else(|| "disjunction selected child is not factual".to_string())?;
        if selected_result.fact().to_string() != selected.to_string()
            || !selected_result.store.infers.is_empty()
        {
            return Err("disjunction selected child changed its proposition or effects".into());
        }
        let Some(selected_proof) =
            self.construct_lean_proof_from_direct_fact_result(selected_result)?
        else {
            return Ok(None);
        };
        Ok(Some(right_associated_disjunction_injection(
            selected_proof,
            evidence.selected_index,
            branches.len(),
        )?))
    }

    /// `Combine`: unfold the exact active concrete predicate proof retained as
    /// the sole child, then select the existential definition clause matching
    /// this Result's target. No Runtime lookup or label reconstruction occurs.
    pub(super) fn construct_lean_definition_projection_from_result(
        &mut self,
        target: &Fact,
        evidence: &DefinitionProjectionBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        let Fact::ExistFact(target_existential) = target else {
            return Err("definition projection requires an existential target".into());
        };
        if !target_existential.is_plain_exist() {
            return Ok(None);
        }
        let [source_result] = subgoals else {
            return Err(
                "definition projection must retain exactly one predicate source Result".into(),
            );
        };
        let source_result = source_result
            .factual_success()
            .ok_or_else(|| "definition projection source child is not factual".to_string())?;
        let source_fact: Fact = evidence.fact.clone().into();
        if source_result.fact().to_string() != source_fact.to_string()
            || !source_result.store.infers.is_empty()
        {
            return Err("definition projection changed its predicate source child".into());
        }

        let definition_name = evidence.definition.name.clone();
        if evidence.fact.predicate.to_string() != definition_name {
            return Err("definition projection evidence names a different predicate".into());
        }
        let binding = self
            .environment_stack
            .predicate_bindings
            .get(&definition_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "definition projection references unavailable predicate `{definition_name}`"
                )
            })?;
        let Some(active_definition) = &binding.definition else {
            return Err("definition projection selected an abstract predicate".into());
        };
        if active_definition.to_string() != evidence.definition.to_string() {
            return Err(
                "definition projection does not match the active predicate definition".into(),
            );
        }

        let components =
            instantiated_predicate_components(&source_fact, &binding, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let clause_index = components
            .iter()
            .position(|component| component == &rendered_target)
            .ok_or_else(|| {
                "definition projection target is not an instantiated definition component"
                    .to_string()
            })?;
        let selector = conjunction_selector(clause_index, components.len())?;
        let Some(source_proof) =
            self.construct_lean_proof_from_direct_fact_result(source_result)?
        else {
            return Ok(None);
        };
        Ok(Some(format!(
            "(by\n  have __definition := {source_proof}\n  unfold {} at __definition\n  exact __definition{selector})",
            binding.lean_name
        )))
    }

    /// `Combine`: consume the base-membership child followed by every checked
    /// set-builder predicate child in source order. The representative used by
    /// Lean is introduced only inside the resulting proof term; the caller's
    /// compiler environment is unchanged.
    pub(super) fn construct_lean_set_builder_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &SetBuilderMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("set-builder membership evidence changed its target".into());
        }
        if subgoals.len() != evidence.expected_premises.len() {
            return Err("set-builder membership lost an ordered child Result".into());
        }
        let mut compiled_children = Vec::with_capacity(subgoals.len());
        for (index, (child, expected)) in subgoals
            .iter()
            .zip(evidence.expected_premises.iter())
            .enumerate()
        {
            let child = child
                .factual_success()
                .ok_or_else(|| format!("set-builder child {index} is not factual"))?;
            if child.fact().to_string() != expected.to_string()
                || child.store.fact.to_string() != expected.to_string()
                || !child.store.infers.is_empty()
            {
                return Err(format!(
                    "set-builder child {index} changed its proposition or published effects"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(child)? else {
                return Ok(None);
            };
            compiled_children.push((expected.clone(), proof));
        }
        Ok(Some(render_set_builder_membership_from_fact_and_proofs(
            target,
            &compiled_children,
            &self.environment_stack,
        )?))
    }

    /// `Wrap`: validate the exact pointwise forall child retained by the
    /// verifier, then package the compiler-constructed function value in the
    /// exact Lean carrier of its function set. The pointwise child is not
    /// discarded: its recursive `ForallProof` shape must agree with the
    /// evidence. The final `In.own` is possible only because rendering the
    /// function value already consumes its Result-owned WD/body evidence and
    /// constructs a value of that exact carrier.
    pub(super) fn construct_lean_function_set_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionSetMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-set membership evidence changed its target".into());
        }
        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-set membership evidence targets a non-membership".into());
        };
        if !matches!(&target_membership.set, Obj::FnSet(_)) {
            return Err("function-set membership evidence retained a non-function set".into());
        }
        let [pointwise_result] = subgoals else {
            return Err(
                "function-set membership evidence requires one pointwise forall child Result"
                    .into(),
            );
        };
        let pointwise_result = pointwise_result
            .factual_success()
            .ok_or_else(|| "function-set membership pointwise child is not factual".to_string())?;
        if pointwise_result.fact().to_string() != evidence.expected_pointwise.to_string()
            || pointwise_result.store.fact.to_string() != evidence.expected_pointwise.to_string()
        {
            return Err("function-set membership changed its pointwise proposition".into());
        }
        let Fact::ForallFact(expected_pointwise) = &evidence.expected_pointwise else {
            return Err(
                "function-set membership retained a non-forall pointwise proposition".into(),
            );
        };
        let SuccessFactProofResult::ForallProof(pointwise_proof) = pointwise_result.proof() else {
            return Err(
                "function-set membership pointwise child lost its ForallProof Result".into(),
            );
        };
        if pointwise_proof.forall_fact.to_string() != expected_pointwise.to_string()
            || pointwise_proof.proves.len() != expected_pointwise.then_facts.len()
        {
            return Err(
                "function-set membership pointwise ForallProof changed its binder or conclusions"
                    .into(),
            );
        }

        let rendered_function = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_function_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_rendered_target =
            format!("Litex.In {rendered_function} {rendered_function_set}");
        if rendered_target != expected_rendered_target {
            return Err("function-set membership changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_function_set} {rendered_function}"
        )))
    }

    /// `Wrap`: validate the verifier-selected head-membership child and use
    /// the exact WD application layer to construct membership in the
    /// instantiated declared return carrier. No function search or return-set
    /// inference is repeated here.
    pub(super) fn construct_lean_function_application_return_membership_from_result(
        &mut self,
        target: &Fact,
        evidence: &FunctionApplicationReturnMembershipBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("function-application return evidence changed its target".into());
        }
        let [head_membership_result] = subgoals else {
            return Err(
                "function-application return evidence requires one head-membership child".into(),
            );
        };
        let head_membership_result = head_membership_result
            .factual_success()
            .ok_or_else(|| "function head-membership child is not factual".to_string())?;
        if head_membership_result.fact().to_string()
            != evidence.expected_head_membership.to_string()
            || !head_membership_result.store.infers.is_empty()
        {
            return Err(
                "function head-membership child changed its proposition or published effects"
                    .into(),
            );
        }
        let Some(_head_membership_proof) =
            self.construct_lean_proof_from_direct_fact_result(head_membership_result)?
        else {
            return Ok(None);
        };

        let Fact::AtomicFact(AtomicFact::InFact(target_membership)) = target else {
            return Err("function-application return evidence targets a non-membership".into());
        };
        let Obj::FnObj(application) = &target_membership.element else {
            return Err("function-application return evidence targets a non-application".into());
        };
        let Fact::AtomicFact(AtomicFact::InFact(head_membership)) =
            &evidence.expected_head_membership
        else {
            return Err("function head contract is not a membership fact".into());
        };
        if !matches!(&head_membership.set, Obj::FnSet(_)) {
            return Err("function head contract retained a non-function carrier".into());
        }
        let application_head: Obj = application.head.as_ref().clone().into();
        if !objs_equal_with_nested_binder_alpha_equivalence(
            &head_membership.element,
            &application_head,
        ) || !objs_equal_with_nested_binder_alpha_equivalence(
            &target_membership.set,
            &evidence.typed_return_set,
        ) {
            return Err("function-application return evidence changed its head or carrier".into());
        }

        let rendered_application = render_obj(&target_membership.element, &self.environment_stack)?;
        let rendered_return_set = render_obj(&target_membership.set, &self.environment_stack)?;
        let rendered_target = render_fact(target, &self.environment_stack)?;
        let expected_target = format!("Litex.In {rendered_application} {rendered_return_set}");
        if rendered_target != expected_target {
            return Err("function-application return evidence changed its rendered target".into());
        }
        Ok(Some(format!(
            "Litex.In.own {rendered_return_set} {rendered_application}"
        )))
    }

    pub(super) fn construct_lean_combined_fact_proof_from_result(
        &mut self,
        target: &Fact,
        combined: &SuccessCombinedFactProofResult,
    ) -> Result<Option<String>, String> {
        if let Some(primary) = combined.primary.as_ref() {
            if primary.fact().to_string() != target.to_string() {
                return Err("combined primary proof changed its target".into());
            }
            for (index, step) in combined.steps.iter().enumerate() {
                let Some(factual) = step.factual_success() else {
                    return Err(format!("combined proof step {index} is not factual"));
                };
                if self
                    .construct_lean_proof_from_direct_fact_result(factual)?
                    .is_none()
                {
                    return Ok(None);
                }
            }
            return self.construct_lean_proof_from_shared_verify_fact_result(primary);
        }

        let components = conjunction_components(target)?;
        if components.len() != combined.steps.len() {
            return Err("combined fact proof changed its component arity".into());
        }
        let mut proofs = Vec::with_capacity(components.len());
        for (component, step) in components.iter().zip(combined.steps.iter()) {
            let factual = step
                .factual_success()
                .ok_or_else(|| "combined proof child is not factual".to_string())?;
            if factual.fact().to_string() != component.to_string() {
                return Err("combined proof child changed its component".into());
            }
            let proof = self.construct_lean_proof_from_direct_fact_result(factual)?;
            let Some(proof) = proof else {
                return Ok(None);
            };
            proofs.push(proof);
        }
        Ok(Some(right_associated_conjunction_proof(&proofs)?))
    }

    pub(super) fn construct_lean_proof_from_shared_verify_fact_result(
        &mut self,
        verification: &SuccessVerifyFactResult,
    ) -> Result<Option<String>, String> {
        let source_fact = verification.fact();
        match verification.proof() {
            SuccessFactProofResult::StoredFactCitation(citation) => {
                self.construct_lean_stored_fact_citation_proof_from_result(&source_fact, citation)
            }
            SuccessFactProofResult::CheckedFunctionDefinitionReduction(result) => self
                .construct_lean_checked_function_definition_reduction_from_result(
                    &source_fact,
                    &result.verification,
                )
                .map(Some),
            SuccessFactProofResult::Strategy(_)
            | SuccessFactProofResult::DefinitionReduction(_)
            | SuccessFactProofResult::DiagnosticOnly(_) => Ok(None),
            SuccessFactProofResult::BuiltinRule(builtin)
            | SuccessFactProofResult::BuiltinStrategy(builtin) => {
                if let Some(BuiltinRuleEvidence::ListSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_list_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RefinedNumericMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_refined_numeric_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::NotEqualSymmetry)
                ) {
                    return self.construct_lean_not_equal_symmetry_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::DisjunctionIntroduction(_))
                ) {
                    let Some(BuiltinRuleEvidence::DisjunctionIntroduction(evidence)) =
                        builtin.evidence.typed()
                    else {
                        unreachable!("disjunction evidence checked above")
                    };
                    return self.construct_lean_disjunction_introduction_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::DefinitionProjection(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_definition_projection_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::SetBuilderMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_builder_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionSetMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_set_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::FunctionApplicationReturnMembership(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_function_application_return_membership_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredLocal(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_local_builtin_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Arithmetic(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_arithmetic_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if matches!(
                    builtin.evidence.typed(),
                    Some(BuiltinRuleEvidence::StandardSetMembershipProjection)
                ) {
                    return self.construct_lean_standard_set_membership_projection_from_result(
                        &source_fact,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RealArithmeticMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_real_arithmetic_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::IntegerMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_integer_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::NaturalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_natural_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RationalMembershipClosure(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_rational_membership_closure_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::Set(rule)) = builtin.evidence.typed() {
                    return self.construct_lean_set_builtin_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::KnownEqualityPath(evidence)) =
                    builtin.evidence.typed()
                {
                    return Ok(Some(self.construct_lean_known_equality_path_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    )?));
                }
                if let Some(BuiltinRuleEvidence::SetRelationDuality(rule)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_set_relation_duality_from_result(
                        &source_fact,
                        *rule,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredReflexivePredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    if !builtin.subgoals.is_empty() {
                        return Err(
                            "shared registered reflexive-predicate proof retained child Results"
                                .into(),
                        );
                    }
                    return Ok(Some(
                        construct_lean_registered_reflexive_predicate_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    ));
                }
                if let Some(BuiltinRuleEvidence::RegisteredSymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_symmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_registered_antisymmetric_predicate_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) =
                    builtin.evidence.typed()
                {
                    return self.construct_lean_complex_algebraic_normalization_from_result(
                        &source_fact,
                        evidence,
                        &builtin.subgoals,
                    );
                }
                if let Some(evidence) = builtin.evidence.typed() {
                    if let Some(limitation) = direct_builtin_rule_compiler_limitation(evidence) {
                        return Err(limitation.to_string());
                    }
                }
                if !builtin.subgoals.is_empty() {
                    return Ok(None);
                }
                match builtin.evidence.typed() {
                    Some(BuiltinRuleEvidence::ObjectReflexivity(evidence)) => {
                        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &source_fact else {
                            return Err(
                                "shared object-reflexivity evidence targets a non-equality fact"
                                    .into(),
                            );
                        };
                        if evidence.expected_target.to_string() != source_fact.to_string()
                            || obj_equality_key(&equality.left) != obj_equality_key(&equality.right)
                        {
                            return Err(
                                "shared object-reflexivity evidence changed its target".into()
                            );
                        }
                        Ok(Some(format!(
                            "Litex.Same.refl {}",
                            render_obj(&equality.left, &self.environment_stack)?
                        )))
                    }
                    Some(BuiltinRuleEvidence::RationalNormalization(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared rational-normalization evidence changed its target".into(),
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
                        validate_success_evaluate_obj_result(&evidence.right_evaluation)?;
                        if evidence.left_evaluation.value.normalized_value
                            != evidence.right_evaluation.value.normalized_value
                        {
                            return Err(
                                "shared rational-normalization retained unequal normal forms"
                                    .into(),
                            );
                        }
                        Ok(Some(
                            "Litex.Same.ofEq (by norm_num [Litex.tupleDim, Litex.TupleShape.dimension])"
                                .into(),
                        ))
                    }
                    Some(BuiltinRuleEvidence::ComplexAlgebraicNormalization(evidence)) => {
                        self.construct_lean_complex_algebraic_normalization_from_result(
                            &source_fact,
                            evidence,
                            &builtin.subgoals,
                        )
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericComparison(evidence)) => {
                        validate_closed_numeric_comparison_builtin_rule_evidence(
                            &source_fact,
                            evidence,
                        )?;
                        Ok(Some(render_closed_numeric_comparison_fact(
                            &source_fact,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::OrderReflexivity(evidence)) => Ok(Some(
                        construct_lean_order_reflexivity_from_result(
                            &source_fact,
                            evidence,
                            &self.environment_stack,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::RuntimeResolvedNumericComparison(evidence)) => self
                        .construct_lean_runtime_resolved_numeric_comparison_from_assignment_result(
                            &source_fact,
                            evidence,
                        )
                        .map(Some),
                    Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) => {
                        if evidence.expected_target.to_string() != source_fact.to_string() {
                            return Err(
                                "shared closed-numeric-membership changed its target".into()
                            );
                        }
                        validate_success_evaluate_obj_result(&evidence.evaluation)?;
                        Ok(Some(render_closed_numeric_membership_from_result(
                            &source_fact,
                            evidence.target_set,
                            &evidence.evaluation,
                            &self.environment_stack,
                        )?))
                    }
                    Some(BuiltinRuleEvidence::ClosedNumericNonmembership(evidence)) => self
                        .construct_lean_closed_numeric_nonmembership_from_result(
                            &source_fact,
                            evidence,
                        ),
                    Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) => Ok(Some(
                        self.construct_lean_standard_set_nonempty_from_result(
                            &source_fact,
                            evidence,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::NativeConstantMembership(rule)) => Ok(Some(
                        self.construct_lean_native_constant_membership_from_result(
                            &source_fact,
                            *rule,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::StandardSetSubset) => Ok(Some(
                        self.construct_lean_standard_set_subset_from_result(&source_fact)?,
                    )),
                    Some(BuiltinRuleEvidence::PrimeU64Reflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            true,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::CoprimeNaturalReflection) => Ok(Some(
                        self.construct_lean_number_theory_reflection_from_result(
                            &source_fact,
                            false,
                        )?,
                    )),
                    Some(BuiltinRuleEvidence::FiniteSet(rule)) => Ok(Some(
                        self.construct_lean_finite_set_from_result(&source_fact, *rule)?,
                    )),
                    Some(BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(rule)) => Ok(
                        Some(self.construct_lean_complex_membership_closure_from_result(
                            &source_fact,
                            *rule,
                        )?),
                    ),
                    Some(BuiltinRuleEvidence::TupleLiteralShape) => Ok(Some(
                        self.construct_lean_tuple_literal_shape_from_result(&source_fact)?,
                    )),
                    None => Ok(None),
                    Some(evidence) => unreachable!(
                        "typed shared builtin evidence must be handled before the terminal direct compiler dispatch: {evidence:?}"
                    ),
                }
            }
            SuccessFactProofResult::CombinedProofs(combined) => {
                self.construct_lean_combined_fact_proof_from_result(&source_fact, combined)
            }
            SuccessFactProofResult::KnownForallInstantiation(instantiation) => self
                .construct_lean_known_forall_instantiation_from_result(&source_fact, instantiation),
            SuccessFactProofResult::Transform(transformation) => self
                .construct_lean_single_fact_transformation_from_result(
                    &source_fact,
                    transformation,
                ),
            SuccessFactProofResult::Reuse(reuse) => {
                self.construct_lean_proof_from_shared_verify_fact_result(reuse.source.as_ref())
            }
            SuccessFactProofResult::ForallProof(_) => Ok(None),
        }
    }

    /// `Wrap`: compile the exact reordered predicate child retained by the
    /// verifier, then replay the registered permutation theorem until the
    /// requested target ordering is reached. Repeating the theorem matters for
    /// non-involutive permutations: the Runtime checks `P(target)`, while a
    /// theorem registered as `source -> P(source)` may need more than one
    /// application to return from that premise to `target`.
    pub(super) fn construct_lean_registered_symmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredSymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered symmetric-predicate evidence changed its target".into());
        }
        let Fact::AtomicFact(target_atomic @ AtomicFact::NormalAtomicFact(target_predicate)) =
            target
        else {
            return Err(
                "registered symmetric-predicate evidence targets a non-user predicate".into(),
            );
        };
        if target_predicate.predicate.to_string() != evidence.predicate_name
            || target_predicate.body.len() < 2
        {
            return Err(
                "registered symmetric-predicate evidence changed its predicate or arity".into(),
            );
        }
        let expected_alternate_from_gather: Fact = target_atomic
            .symmetric_reordered_args(&evidence.gather)
            .ok_or_else(|| {
                "registered symmetric-predicate evidence retained an invalid permutation"
                    .to_string()
            })?
            .into();
        if expected_alternate_from_gather.to_string() != evidence.expected_alternate.to_string() {
            return Err(
                "registered symmetric-predicate evidence changed its reordered premise".into(),
            );
        }
        let [alternate_result] = subgoals else {
            return Err(
                "registered symmetric-predicate proof requires exactly one child Result".into(),
            );
        };
        let alternate_result = alternate_result
            .factual_success()
            .ok_or_else(|| "registered symmetric-predicate child is not factual".to_string())?;
        if alternate_result.fact().to_string() != evidence.expected_alternate.to_string()
            || alternate_result.store.fact.to_string() != evidence.expected_alternate.to_string()
            || !alternate_result.store.infers.is_empty()
        {
            return Err(
                "registered symmetric-predicate child changed its fact or published effects".into(),
            );
        }

        let bindings = self
            .environment_stack
            .registered_symmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .ok_or_else(|| {
                format!(
                    "registered symmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let mut selected_binding = None;
        for binding in bindings.iter().rev() {
            let binding_gather = registered_symmetric_predicate_gather(
                &binding.forall_fact,
                &evidence.predicate_name,
            )?;
            if binding_gather == evidence.gather {
                selected_binding = Some(binding.clone());
                break;
            }
        }
        let binding = selected_binding.ok_or_else(|| {
            format!(
                "registered symmetry theorem for `{}` does not own permutation {:?}",
                evidence.predicate_name, evidence.gather
            )
        })?;

        render_fact(target, &self.environment_stack)?;
        let Some(mut proof) =
            self.construct_lean_proof_from_direct_fact_result(alternate_result)?
        else {
            return Ok(None);
        };
        let mut current = evidence.expected_alternate.clone();
        let mut visited = HashSet::new();
        visited.insert(current.to_string());
        loop {
            let (next, parameter_arguments) =
                instantiate_registered_symmetric_predicate_transition(
                    &binding.forall_fact,
                    &evidence.predicate_name,
                    &current,
                )?;
            let mut theorem_application = binding.theorem_name.clone();
            for argument in parameter_arguments {
                theorem_application.push(' ');
                theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
            }
            theorem_application.push_str(&format!(" ({proof})"));
            proof = theorem_application;
            if next.to_string() == target.to_string() {
                return Ok(Some(proof));
            }
            if !visited.insert(next.to_string()) {
                return Err(
                    "registered symmetric-predicate permutation cycled without reaching its target"
                        .into(),
                );
            }
            current = next;
        }
    }

    /// `Combine`: compile the two ordered predicate-premise children and apply
    /// the exact antisymmetry theorem currently visible in the compiler
    /// environment created by an earlier registration Result.
    pub(super) fn construct_lean_registered_antisymmetric_predicate_from_result(
        &mut self,
        target: &Fact,
        evidence: &RegisteredAntisymmetricPredicateBuiltinRuleEvidence,
        subgoals: &[StmtResult],
    ) -> Result<Option<String>, String> {
        if evidence.expected_target.to_string() != target.to_string() {
            return Err("registered antisymmetric-predicate evidence changed its target".into());
        }
        let binding = self
            .environment_stack
            .registered_antisymmetric_predicate_theorem_bindings
            .get(&evidence.predicate_name)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "registered antisymmetry theorem for `{}` is not visible in this compiler environment",
                    evidence.predicate_name
                )
            })?;
        let (parameter_arguments, expected_premises) =
            instantiate_registered_antisymmetric_predicate_application(
                &binding.forall_fact,
                &evidence.predicate_name,
                target,
            )?;
        if subgoals.len() != expected_premises.len() {
            return Err(
                "registered antisymmetric-predicate proof lost an ordered child Result".into(),
            );
        }
        let mut premise_proofs = Vec::with_capacity(subgoals.len());
        for (index, (subgoal, expected)) in
            subgoals.iter().zip(expected_premises.iter()).enumerate()
        {
            let subgoal = subgoal.factual_success().ok_or_else(|| {
                format!("registered antisymmetric-predicate child {index} is not factual")
            })?;
            if subgoal.fact().to_string() != expected.to_string()
                || subgoal.store.fact.to_string() != expected.to_string()
                || !subgoal.store.infers.is_empty()
            {
                return Err(format!(
                    "registered antisymmetric-predicate child {index} changed its fact or published effects"
                ));
            }
            let Some(proof) = self.construct_lean_proof_from_direct_fact_result(subgoal)? else {
                return Ok(None);
            };
            premise_proofs.push(proof);
        }

        render_fact(target, &self.environment_stack)?;
        let mut theorem_application = binding.theorem_name;
        for argument in parameter_arguments {
            theorem_application.push(' ');
            theorem_application.push_str(&render_obj(&argument, &self.environment_stack)?);
        }
        for proof in premise_proofs {
            theorem_application.push_str(&format!(" ({proof})"));
        }
        Ok(Some(theorem_application))
    }

    pub(super) fn compile_stmt_results_in_new_local_environment(
        &mut self,
        results: &[StmtResult],
    ) -> Result<Vec<String>, String> {
        self.environment_stack.push_inherited_environment();
        let outer_declarations = mem::take(&mut self.declarations);
        let outer_fact_name_index = mem::replace(&mut self.next_fact_name_index, 0);
        let outer_sketch_namespace_index = mem::replace(&mut self.next_sketch_namespace_index, 0);

        let compilation = results
            .iter()
            .try_for_each(|result| self.compile_stmt_result_to_lean_source(result));
        let nested_declarations = mem::take(&mut self.declarations);

        self.declarations = outer_declarations;
        self.next_fact_name_index = outer_fact_name_index;
        self.next_sketch_namespace_index = outer_sketch_namespace_index;
        self.environment_stack.pop_local_environment();

        compilation?;
        Ok(nested_declarations)
    }

    /// Construct one child fact proof without publishing its store effect.
    /// Direct Result evidence is the only accepted proof source.
    pub(super) fn construct_lean_proof_from_fact_result_without_storing(
        &mut self,
        result: &StmtResult,
        expected_fact: &Fact,
        role: &str,
    ) -> Result<String, String> {
        let factual = result
            .factual_success()
            .ok_or_else(|| format!("{role} is not a successful fact Result"))?;
        if factual.fact().to_string() != expected_fact.to_string() {
            return Err(format!(
                "{role} changed `{expected_fact}` to `{}`",
                factual.fact()
            ));
        }
        if !factual.store.infers.is_empty() {
            return Err(format!("{role} unexpectedly published inference effects"));
        }
        if let Some(proof) =
            self.construct_lean_proof_from_direct_fact_result_using_its_well_definedness(factual)?
        {
            return Ok(proof);
        }
        Err(format!(
            "StmtResult-to-Lean compiler has no direct proof consumer for `{expected_fact}`"
        ))
    }

    pub(super) fn finish_lean_source(mut self) -> Result<String, String> {
        if !self.environment_stack.is_top_level() {
            return Err(
                "StmtResultToLeanCompiler finished with an unclosed local environment".into(),
            );
        }
        if let Some(namespace) = self.open_clear_namespace.take() {
            self.declarations.push(format!("end {namespace}"));
        }

        let file_name = Path::new(&self.source_label)
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid source label `{}`", self.source_label))?;
        let stem = Path::new(file_name)
            .file_stem()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid source label `{}`", self.source_label))?;
        let namespace = format!("__Compiler_{}", lean_identifier(stem));
        Ok(format!(
            "-- Generated by StmtResultToLeanCompiler from {file_name}. DO NOT EDIT.\n\
             import Litex\n\n\
             set_option linter.style.nameCheck false\n\n\
             namespace {namespace}\n\n{}\n\n\
             end {namespace}\n",
            self.declarations.join("\n\n")
        ))
    }
}
