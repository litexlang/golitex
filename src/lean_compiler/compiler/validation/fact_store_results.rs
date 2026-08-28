//! Fact-store output and typed inference completeness validation.

use super::super::*;

pub(in super::super) fn validate_single_fact_store_output(
    infer_result: &SuccessInferResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if !infer_result.rule_applications.is_empty() {
        return Err(format!(
            "{result_layer} unexpectedly retained typed inference rules"
        ));
    }
    let [output] = infer_result.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one store output"
        ));
    };
    if output.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string()
        || !output.inferred_facts.is_empty()
        || !output.inferred_fact_ids.is_empty()
    {
        return Err(format!(
            "{result_layer} changed its stored fact or retained inferred children"
        ));
    }
    output
        .fact_id
        .ok_or_else(|| format!("{result_layer} store has no FactId"))
}

pub(in super::super) fn validate_single_fact_store_output_allowing_supported_typed_inferences(
    infer_result: &SuccessInferResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if infer_result.rule_applications.iter().any(|application| {
        !defined_predicate_infer_rule(&application.rule)
            && !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
    }) {
        return Err(format!(
            "{result_layer} retained an unsupported typed inference rule"
        ));
    }
    validate_typed_infer_result_identity_completeness(infer_result, result_layer)?;
    let fact_ids = exact_ordered_fact_ids_from_store_results(
        infer_result,
        std::slice::from_ref(expected_fact),
        result_layer,
    )?;
    let [fact_id] = fact_ids.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one direct store output"
        ));
    };
    Ok(*fact_id)
}

pub(in super::super) fn validate_conjunction_store_and_component_inference_results(
    infer_result: &SuccessInferResult,
    source_fact: &Fact,
    expected_components: &[Fact],
    result_layer: &str,
) -> Result<(FactId, Vec<FactId>), String> {
    let [source_output] = infer_result.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one source store"
        ));
    };
    let source_fact_id = source_output
        .fact_id
        .ok_or_else(|| format!("{result_layer} source store has no FactId"))?;
    if source_output.itself_and_why_itself_is_stored.0.to_string() != source_fact.to_string()
        || source_output.inferred_facts.len() != source_output.inferred_fact_ids.len()
        || infer_result.rule_applications.len() != expected_components.len()
    {
        return Err(format!(
            "{result_layer} changed its source or component inference arity"
        ));
    }

    let advertised_facts = source_output
        .inferred_facts
        .iter()
        .zip(source_output.inferred_fact_ids.iter())
        .map(|(fact, fact_id)| {
            Ok((
                fact_id.ok_or_else(|| {
                    format!("{result_layer} advertised an inferred fact without FactId")
                })?,
                fact.to_string(),
            ))
        })
        .collect::<Result<HashSet<_>, String>>()?;
    if advertised_facts.len() != source_output.inferred_facts.len() {
        return Err(format!(
            "{result_layer} advertised a duplicate inferred fact identity"
        ));
    }

    let mut component_fact_ids = Vec::with_capacity(expected_components.len());
    let mut recursively_owned_facts = HashSet::new();
    for (component_index, expected_component) in expected_components.iter().enumerate() {
        let application = &infer_result.rule_applications[component_index];
        let InferRule::ConjunctionImpliesComponent(rule) = &application.rule else {
            return Err(format!(
                "{result_layer} component {component_index} retained another infer rule"
            ));
        };
        if rule.component_index != component_index
            || rule.component_count != expected_components.len()
        {
            return Err(format!(
                "{result_layer} changed component {component_index}'s structural position"
            ));
        }
        let [premise] = application.premises.as_slice() else {
            return Err(format!(
                "{result_layer} component {component_index} must retain one premise"
            ));
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err(format!(
                "{result_layer} component {component_index} changed its conjunction premise"
            ));
        }
        let [conclusion] = application.conclusions.as_slice() else {
            return Err(format!(
                "{result_layer} component {component_index} must retain one conclusion"
            ));
        };
        let component_fact_id = conclusion
            .fact_id
            .ok_or_else(|| format!("{result_layer} component {component_index} has no FactId"))?;
        validate_conjunction_component_inference_target(rule, &premise.fact, &conclusion.fact)?;
        if conclusion.fact.to_string() != expected_component.to_string()
            || !advertised_facts.contains(&(component_fact_id, conclusion.fact.to_string()))
        {
            return Err(format!(
                "{result_layer} component {component_index} changed its conclusion Result"
            ));
        }
        if conclusion
            .infers
            .rule_applications
            .iter()
            .any(|application| !defined_predicate_infer_rule(&application.rule))
        {
            return Err(format!(
                "{result_layer} component {component_index} retained unsupported nested inference"
            ));
        }
        validate_typed_infer_result_identity_completeness(
            &conclusion.infers,
            &format!("{result_layer} component {component_index}"),
        )?;
        let [component_store] = conclusion.infers.store_fact_outputs.as_slice() else {
            return Err(format!(
                "{result_layer} component {component_index} lost its recursive store"
            ));
        };
        if component_store.fact_id != Some(component_fact_id)
            || component_store
                .itself_and_why_itself_is_stored
                .0
                .to_string()
                != expected_component.to_string()
            || component_store.inferred_facts.len() != component_store.inferred_fact_ids.len()
        {
            return Err(format!(
                "{result_layer} component {component_index} recursive store changed"
            ));
        }
        recursively_owned_facts.insert((component_fact_id, conclusion.fact.to_string()));
        collect_infer_result_fact_identities(&conclusion.infers, &mut recursively_owned_facts)?;
        component_fact_ids.push(component_fact_id);
    }
    if !advertised_facts.is_subset(&recursively_owned_facts) {
        return Err(format!(
            "{result_layer} advertised an inferred fact outside its component Result trees"
        ));
    }
    Ok((source_fact_id, component_fact_ids))
}

pub(in super::super) fn validate_success_store_fact_result(
    store: &SuccessStoreFactResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if store.fact.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its source fact"));
    }
    let fact_id = store
        .fact_id
        .ok_or_else(|| format!("{result_layer} has no FactId"))?;
    let output_fact_id =
        validate_single_fact_store_output(&store.infers, expected_fact, result_layer)?;
    if output_fact_id != fact_id {
        return Err(format!(
            "{result_layer} store Result and store output disagree on FactId"
        ));
    }
    Ok(fact_id)
}

/// Quantified-conclusion WD checks temporarily store the checked proposition
/// and may run ordinary definition inference in that preflight scope. Those
/// inferred children are not proof premises for the final conclusion, but
/// their exact identities still have to be structurally complete.
pub(in super::super) fn validate_success_store_fact_result_allowing_well_definedness_inferred_children(
    store: &SuccessStoreFactResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if store.fact.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its source fact"));
    }
    let fact_id = store
        .fact_id
        .ok_or_else(|| format!("{result_layer} has no FactId"))?;
    if let Fact::AndFact(and_fact) = expected_fact {
        validate_conjunction_well_definedness_preflight_store(store, and_fact, result_layer)?;
        return Ok(fact_id);
    }
    if store.infers.rule_applications.iter().any(|application| {
        !defined_predicate_infer_rule(&application.rule)
            && !infer_rule_has_direct_compiler_environment_consumer(&application.rule)
    }) {
        return Err(format!(
            "{result_layer} retained an unsupported typed inference rule"
        ));
    }
    validate_typed_infer_result_identity_completeness(&store.infers, result_layer)?;
    let [output] = store.infers.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one store output"
        ));
    };
    if output.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string()
        || output.fact_id != Some(fact_id)
        || output.inferred_facts.len() != output.inferred_fact_ids.len()
    {
        return Err(format!(
            "{result_layer} changed its stored fact, FactId, or inferred child arity"
        ));
    }
    let mut retained_ids = HashSet::new();
    retained_ids.insert(fact_id);
    for (inferred_fact, inferred_fact_id) in output
        .inferred_facts
        .iter()
        .zip(output.inferred_fact_ids.iter())
    {
        let inferred_fact_id = inferred_fact_id.ok_or_else(|| {
            format!("{result_layer} inferred fact `{inferred_fact}` has no FactId")
        })?;
        if !retained_ids.insert(inferred_fact_id) {
            return Err(format!(
                "{result_layer} reused FactId `{inferred_fact_id}` for multiple stored facts"
            ));
        }
    }
    Ok(fact_id)
}

pub(in super::super) fn validate_conjunction_well_definedness_preflight_store(
    store: &SuccessStoreFactResult,
    expected_and_fact: &AndFact,
    result_layer: &str,
) -> Result<(), String> {
    let source_fact: Fact = expected_and_fact.clone().into();
    let source_fact_id = store
        .fact_id
        .ok_or_else(|| format!("{result_layer} has no conjunction FactId"))?;
    let [source_output] = store.infers.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} must retain exactly one conjunction source store"
        ));
    };
    if source_output.fact_id != Some(source_fact_id)
        || source_output.itself_and_why_itself_is_stored.0.to_string() != source_fact.to_string()
        || source_output.inferred_facts.len() != source_output.inferred_fact_ids.len()
    {
        return Err(format!(
            "{result_layer} changed its conjunction source or inferred identity arity"
        ));
    }
    validate_typed_infer_result_identity_completeness(&store.infers, result_layer)?;

    let advertised_components = source_output
        .inferred_facts
        .iter()
        .zip(source_output.inferred_fact_ids.iter())
        .map(|(fact, fact_id)| {
            Ok((
                fact_id.ok_or_else(|| {
                    format!("{result_layer} advertised a conjunction component without FactId")
                })?,
                fact.to_string(),
            ))
        })
        .collect::<Result<HashSet<_>, String>>()?;
    if advertised_components.len() != source_output.inferred_facts.len() {
        return Err(format!(
            "{result_layer} advertised a duplicate conjunction component"
        ));
    }

    let mut inferred_component_indices = HashSet::new();
    let mut recursively_owned_components = HashSet::new();
    for (application_index, application) in store.infers.rule_applications.iter().enumerate() {
        let InferRule::ConjunctionImpliesComponent(rule) = &application.rule else {
            return Err(format!(
                "{result_layer} application {application_index} is not a conjunction projection"
            ));
        };
        if rule.component_count != expected_and_fact.facts.len()
            || rule.component_index >= expected_and_fact.facts.len()
            || !inferred_component_indices.insert(rule.component_index)
        {
            return Err(format!(
                "{result_layer} application {application_index} changed or repeated its component position"
            ));
        }
        let [premise] = application.premises.as_slice() else {
            return Err(format!(
                "{result_layer} application {application_index} must retain one source premise"
            ));
        };
        if premise.fact_id != Some(source_fact_id)
            || premise.fact.to_string() != source_fact.to_string()
        {
            return Err(format!(
                "{result_layer} application {application_index} changed its conjunction premise"
            ));
        }
        let [conclusion] = application.conclusions.as_slice() else {
            return Err(format!(
                "{result_layer} application {application_index} must retain one component conclusion"
            ));
        };
        let expected_component: Fact = expected_and_fact.facts[rule.component_index].clone().into();
        let conclusion_fact_id = conclusion.fact_id.ok_or_else(|| {
            format!("{result_layer} application {application_index} conclusion has no FactId")
        })?;
        validate_conjunction_component_inference_target(rule, &premise.fact, &conclusion.fact)?;
        if conclusion.fact.to_string() != expected_component.to_string()
            || !advertised_components.contains(&(conclusion_fact_id, conclusion.fact.to_string()))
            || conclusion
                .infers
                .rule_applications
                .iter()
                .any(|nested| !defined_predicate_infer_rule(&nested.rule))
        {
            return Err(format!(
                "{result_layer} application {application_index} changed its component Result"
            ));
        }
        recursively_owned_components.insert((conclusion_fact_id, conclusion.fact.to_string()));
        collect_infer_result_fact_identities(
            &conclusion.infers,
            &mut recursively_owned_components,
        )?;
    }
    if !advertised_components.is_subset(&recursively_owned_components) {
        return Err(format!(
            "{result_layer} advertised an effect outside its recursive component Results"
        ));
    }
    Ok(())
}

pub(in super::super) fn collect_infer_result_fact_identities(
    infer_result: &SuccessInferResult,
    identities: &mut HashSet<(FactId, String)>,
) -> Result<(), String> {
    for output in &infer_result.store_fact_outputs {
        let source_fact_id = output
            .fact_id
            .ok_or_else(|| "recursive infer store has no source FactId".to_string())?;
        identities.insert((
            source_fact_id,
            output.itself_and_why_itself_is_stored.0.to_string(),
        ));
        for (fact, fact_id) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
        {
            identities.insert((
                fact_id.ok_or_else(|| {
                    "recursive infer store advertised a fact without FactId".to_string()
                })?,
                fact.to_string(),
            ));
        }
    }
    for application in &infer_result.rule_applications {
        for conclusion in &application.conclusions {
            identities.insert((
                conclusion
                    .fact_id
                    .ok_or_else(|| "recursive infer conclusion has no FactId".to_string())?,
                conclusion.fact.to_string(),
            ));
            collect_infer_result_fact_identities(&conclusion.infers, identities)?;
        }
    }
    Ok(())
}

pub(in super::super) fn validate_typed_infer_result_identity_completeness(
    result: &SuccessInferResult,
    result_layer: &str,
) -> Result<(), String> {
    for (store_index, output) in result.store_fact_outputs.iter().enumerate() {
        if output.fact_id.is_none()
            || output.inferred_facts.len() != output.inferred_fact_ids.len()
            || output.inferred_fact_ids.iter().any(Option::is_none)
        {
            return Err(format!(
                "{result_layer} store {store_index} has incomplete frozen fact identities"
            ));
        }
    }
    for (application_index, application) in result.rule_applications.iter().enumerate() {
        if application
            .premises
            .iter()
            .any(|premise| premise.fact_id.is_none())
        {
            return Err(format!(
                "{result_layer} typed application {application_index} has a premise without FactId"
            ));
        }
        for (conclusion_index, conclusion) in application.conclusions.iter().enumerate() {
            if conclusion.fact_id.is_none() {
                return Err(format!(
                    "{result_layer} typed application {application_index} conclusion {conclusion_index} has no FactId"
                ));
            }
            validate_typed_infer_result_identity_completeness(&conclusion.infers, result_layer)?;
        }
    }
    Ok(())
}

/// Select the inference children whose source assumptions remain visible in
/// one reduced-binder forall publication. The complete Result is validated
/// first; the returned value is only a short-lived compiler work value used
/// by the existing typed-inference consumer.
pub(in super::super) fn select_typed_inference_results_for_visible_forall_sources(
    result: &SuccessInferResult,
    complete_sources: &[(FactId, Fact)],
    visible_sources: &[(FactId, Fact)],
    result_layer: &str,
) -> Result<SuccessInferResult, String> {
    validate_typed_infer_result_identity_completeness(result, result_layer)?;
    let complete_source_keys = complete_sources
        .iter()
        .map(|(fact_id, fact)| (*fact_id, fact.to_string()))
        .collect::<HashSet<_>>();
    let visible_source_keys = visible_sources
        .iter()
        .map(|(fact_id, fact)| (*fact_id, fact.to_string()))
        .collect::<HashSet<_>>();

    for (store_index, output) in result.store_fact_outputs.iter().enumerate() {
        let source_key = (
            output
                .fact_id
                .expect("identity completeness validated above"),
            output.itself_and_why_itself_is_stored.0.to_string(),
        );
        if !complete_source_keys.contains(&source_key) {
            return Err(format!(
                "{result_layer} store {store_index} is not owned by its complete forall assumption Result"
            ));
        }
    }
    for (application_index, application) in result.rule_applications.iter().enumerate() {
        let Some(source_premise) = application.premises.first() else {
            return Err(format!(
                "{result_layer} application {application_index} has no source premise"
            ));
        };
        let source_key = (
            source_premise
                .fact_id
                .expect("identity completeness validated above"),
            source_premise.fact.to_string(),
        );
        if !complete_source_keys.contains(&source_key) {
            return Err(format!(
                "{result_layer} application {application_index} cites a source outside its complete forall assumption Result"
            ));
        }
    }

    Ok(SuccessInferResult {
        store_fact_outputs: result
            .store_fact_outputs
            .iter()
            .filter(|output| {
                visible_source_keys.contains(&(
                    output
                        .fact_id
                        .expect("identity completeness validated above"),
                    output.itself_and_why_itself_is_stored.0.to_string(),
                ))
            })
            .cloned()
            .collect(),
        rule_applications: result
            .rule_applications
            .iter()
            .filter(|application| {
                let source_premise = application
                    .premises
                    .first()
                    .expect("source premise validated above");
                visible_source_keys.contains(&(
                    source_premise
                        .fact_id
                        .expect("identity completeness validated above"),
                    source_premise.fact.to_string(),
                ))
            })
            .cloned()
            .collect(),
    })
}
