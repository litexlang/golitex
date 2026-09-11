//! Template definition compilation.

use super::super::*;

impl StmtResultToLeanCompiler {
    pub(in super::super) fn compile_template_definition_stmt_result_to_lean_source(
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
                &self.runtime,
                value.clone(),
                defined_type,
                body.statement.line_file.clone(),
            );
            let factual_type_check = type_check.verified().ok_or_else(|| {
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
            {
                return Err(
                    "Template set-alias body type check changed its typed rule or children".into(),
                );
            }

            let defined_object: Obj =
                Identifier::new_bound(defined_binding.name().to_string(), defined_binding.as_ref())
                    .into();
            let expected_stores = vec![
                object_type_fact_for_compiler_definition(
                    &self.runtime,
                    defined_object.clone(),
                    defined_type,
                    body.statement.line_file.clone(),
                ),
                self.runtime
                    .new_equal_fact(
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
}
