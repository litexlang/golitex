//! Template instantiation result installation.

use super::super::*;

pub(in super::super) fn install_template_instantiation_result(
    expected_object: &Obj,
    result: &SuccessTemplateInstantiationResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let application = match result {
        SuccessTemplateInstantiationResult::Reused(result) => &result.application,
        SuccessTemplateInstantiationResult::Created(result) => &result.application,
    };
    let Obj::InstantiatedTemplateObj(expected_application) = expected_object else {
        return Err("Template instantiation Result is attached to a non-Template object".into());
    };
    if expected_application.template_name.to_string() != application.template_name.to_string()
        || expected_application.args.len() != application.args.len()
        || expected_application
            .args
            .iter()
            .zip(application.args.iter())
            .any(|(expected, retained)| obj_equality_key(expected) != obj_equality_key(retained))
    {
        return Err("Template instantiation Result changed its exact application identity".into());
    }
    let template_name = application.template_name.to_string();
    let binding = environment_stack
        .template_set_alias_bindings
        .get(&template_name)
        .cloned()
        .ok_or_else(|| {
            format!("Template application `{application}` has no compiled definition")
        })?;
    if application.args.len() != binding.parameter_count {
        return Err(format!(
            "Template application `{application}` changed its compiled argument count"
        ));
    }
    let arguments = application
        .args
        .iter()
        .map(|argument| render_obj(argument, environment_stack))
        .collect::<Result<Vec<_>, _>>()?;
    let rendered_application = format!("({} {})", binding.lean_name, arguments.join(" "));
    let SuccessTemplateInstantiationResult::Created(created) = result else {
        return Ok(());
    };
    if created.template_argument_results.len() != application.args.len()
        || !created.template_domain_results.is_empty()
    {
        return Err(
            "created Template instance changed its argument or unsupported domain Result count"
                .into(),
        );
    }
    for (argument_index, (argument, argument_result)) in application
        .args
        .iter()
        .zip(created.template_argument_results.iter())
        .enumerate()
    {
        if argument_result.argument_index != argument_index
            || obj_equality_key(&argument_result.argument) != obj_equality_key(argument)
            || !matches!(argument_result.expected_type, ParamType::Set(_))
        {
            return Err(format!(
                "Template argument Result {argument_index} changed its identity or set type"
            ));
        }
        validate_success_obj_fact_check(&argument_result.verification)?;
        let expected: Fact = IsSetFact::new(
            argument.clone(),
            argument_result
                .verification
                .expected_proposition
                .line_file(),
        )
        .into();
        if expected.to_string()
            != argument_result
                .verification
                .expected_proposition
                .to_string()
        {
            return Err(format!(
                "Template argument Result {argument_index} changed its set proposition"
            ));
        }
    }

    let SuccessStmtResult::Definition(SuccessDefinitionStmtResult::HaveObjEqualStmt(body)) =
        created.body_statement_result.as_ref()
    else {
        return Err("created Template instance retained a non-set-alias body Result".into());
    };
    let body_bindings = body.statement.param_def.collect_param_bindings_with_types();
    let [(defined_binding, defined_type @ ParamType::Set(_))] = body_bindings.as_slice() else {
        return Err("created Template instance body no longer defines one set alias".into());
    };
    let [value] = body.statement.objs_equal_to.as_slice() else {
        return Err("created Template instance body changed its one value".into());
    };
    if let Some(previous) = environment_stack
        .symbol_names
        .insert(defined_binding.id(), rendered_application.clone())
    {
        if previous != rendered_application {
            return Err("created Template body changed its application SymbolId binding".into());
        }
    }
    let defined_object: Obj =
        Identifier::new_bound(defined_binding.name().to_string(), defined_binding.as_ref()).into();
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
    if body.common.infers.store_fact_outputs.len() != expected_stores.len()
        || body
            .common
            .infers
            .store_fact_outputs
            .iter()
            .zip(expected_stores.iter())
            .any(|(stored, expected)| {
                stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string()
                    || stored.fact_id.is_some()
                    || !stored.inferred_facts.is_empty()
                    || !stored.inferred_fact_ids.is_empty()
            })
    {
        return Err(
            "created Template instance body changed its preverified, non-public store Results"
                .into(),
        );
    }
    let rendered_value = render_set_definition_value(
        &LeanTargetObjectRepresentation::lower(value)?,
        environment_stack,
    )?;

    let Fact::AtomicFact(AtomicFact::EqualFact(surface_equality)) = &created.surface_equality.fact
    else {
        return Err("Template surface equality changed to a non-equality fact".into());
    };
    let hidden_identifier = if matches!(surface_equality.left, Obj::InstantiatedTemplateObj(_)) {
        &surface_equality.right
    } else if matches!(surface_equality.right, Obj::InstantiatedTemplateObj(_)) {
        &surface_equality.left
    } else {
        return Err("Template surface equality lost its public application endpoint".into());
    };
    let Obj::Atom(_) = hidden_identifier else {
        return Err("Template surface equality hidden endpoint is not an identifier".into());
    };
    if !hidden_identifier
        .to_string()
        .ends_with(&application.surface_name())
    {
        return Err("Template surface equality changed its hidden instance name".into());
    }
    let surface_fact_id = created
        .surface_equality
        .fact_id
        .ok_or_else(|| "Template surface equality has no frozen FactId".to_string())?;
    if !created
        .surface_equality
        .infers
        .store_fact_outputs
        .iter()
        .any(|output| {
            output.fact_id == Some(surface_fact_id)
                && output.itself_and_why_itself_is_stored.0.to_string()
                    == created.surface_equality.fact.to_string()
        })
    {
        return Err("Template surface equality lost its exact store Result".into());
    }

    for store in &created.public_value_equalities {
        let role = "public value equality";
        let fact_id = store
            .fact_id
            .ok_or_else(|| format!("Template {role} has no frozen FactId"))?;
        let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = &store.fact else {
            return Err(format!("Template {role} changed to a non-equality fact"));
        };
        let rendered_left = render_obj(&equality.left, environment_stack)?;
        let rendered_right = render_obj(&equality.right, environment_stack)?;
        if rendered_left != rendered_application && rendered_right != rendered_application {
            return Err(format!(
                "Template {role} no longer mentions its exact compiled application"
            ));
        }
        environment_stack
            .fact_names
            .insert(fact_id, format!("Litex.Same.refl {rendered_value}"));
        environment_stack
            .fact_propositions
            .insert(fact_id, store.fact.clone());
    }
    if !created.supplemental_stores.is_empty() || created.registered_set_builder.is_some() {
        return Err(
            "direct Template set-alias compiler does not support supplemental stores or set builders"
                .into(),
        );
    }
    Ok(())
}
