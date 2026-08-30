//! Fact well-definedness results and direct universal publication.

use super::super::*;

pub(in super::super) fn validate_scoped_fact_check_result(
    result: &SuccessFactStmtResult,
    expected_fact: &Fact,
    result_layer: &str,
) -> Result<(), String> {
    if result.store.fact.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its checked fact"));
    }
    if result.store.infers.is_empty() {
        return Ok(());
    }
    let [output] = result.store.infers.store_fact_outputs.as_slice() else {
        return Err(format!(
            "{result_layer} retained an invalid number of direct store outputs"
        ));
    };
    if output.itself_and_why_itself_is_stored.0.to_string() != expected_fact.to_string() {
        return Err(format!("{result_layer} changed its direct store output"));
    }
    if let (Some(result_fact_id), Some(output_fact_id)) = (result.store.fact_id, output.fact_id) {
        if result_fact_id != output_fact_id {
            return Err(format!(
                "{result_layer} store Result and direct output disagree on FactId"
            ));
        }
    }
    Ok(())
}

pub(in super::super) fn fact_is_supported_by_direct_named_theorem(fact: &Fact) -> bool {
    match fact {
        Fact::AtomicFact(_) => true,
        Fact::AndFact(and_fact) => !and_fact.facts.is_empty(),
        Fact::ExistFact(existential) => {
            if !existential.is_plain_exist()
                || existential.typed_parameters().number_of_params() != 1
                || existential.facts().len() != 1
            {
                return false;
            }
            let group = &existential.typed_parameters().groups[0];
            group.params.len() == 1
                && matches!(group.param_type, ParamType::Obj(_))
                && matches!(
                    existential.facts()[0].from_ref_to_cloned_fact(),
                    Fact::AtomicFact(_)
                )
        }
        _ => false,
    }
}

pub(in super::super) fn validate_direct_named_theorem_conclusion_well_definedness(
    result: &SuccessVerifyFactWellDefinedProofResult,
    expected_fact: &Fact,
) -> Result<(), String> {
    if matches!(expected_fact, Fact::AtomicFact(_)) {
        return validate_atomic_fact_well_definedness_proof_result(result, expected_fact);
    }
    if let Fact::AndFact(expected_and_fact) = expected_fact {
        let SuccessVerifyFactWellDefinedProofResult::AndFact(result) = result else {
            return Err("conjunction theorem conclusion has no conjunction WD Result".into());
        };
        if result.statement.to_string() != expected_and_fact.to_string()
            || result.conjuncts.len() != expected_and_fact.facts.len()
        {
            return Err("conjunction theorem conclusion WD changed its source structure".into());
        }
        for (conjunct_index, (conjunct, expected_conjunct)) in result
            .conjuncts
            .iter()
            .zip(expected_and_fact.facts.iter())
            .enumerate()
        {
            validate_atomic_fact_well_definedness_proof_result(
                conjunct,
                &expected_conjunct.clone().into(),
            )
            .map_err(|error| {
                format!("conjunction theorem conclusion child {conjunct_index}: {error}")
            })?;
        }
        return Ok(());
    }
    if let Fact::ForallFact(expected_forall) = expected_fact {
        return validate_nested_forall_fact_well_definedness(result, expected_forall);
    }
    let Fact::ExistFact(expected_existential) = expected_fact else {
        return Err("direct named theorem received an unsupported conclusion family".into());
    };
    let SuccessVerifyFactWellDefinedProofResult::ExistFact(result) = result else {
        return Err("existential theorem conclusion has no existential WD Result".into());
    };
    if result.statement.to_string() != expected_existential.to_string()
        || result.binder.parameter_groups.len() != 1
        || result.body.len() != 1
    {
        return Err("existential theorem conclusion WD changed its source structure".into());
    }
    let expected_group = &expected_existential.typed_parameters().groups[0];
    let actual_group = &result.binder.parameter_groups[0];
    if actual_group.group_index != 0
        || actual_group.parameter_type.to_string() != expected_group.param_type.to_string()
        || actual_group.parameters.len() != 1
        || expected_group.params.len() != 1
    {
        return Err("existential theorem conclusion WD changed its binder mapping".into());
    }
    let parameter = &actual_group.parameters[0];
    if parameter.symbol_id != Some(expected_group.params[0].id()) {
        return Err("existential theorem conclusion WD changed its binder SymbolId".into());
    }
    let expected_set = parameter_set(&expected_group.param_type)?;
    validate_object_parameter_premise(
        expected_group.params[0].id(),
        expected_set,
        &parameter.proposition,
    )?;
    validate_atomic_fact_well_definedness_result(
        parameter.well_definedness.as_ref(),
        &parameter.proposition,
    )?;
    validate_single_fact_store_output_allowing_supported_typed_inferences(
        &parameter.infers,
        &parameter.proposition,
        "existential theorem conclusion binder WD",
    )?;

    let expected_body = expected_existential.facts()[0].from_ref_to_cloned_fact();
    let body = &result.body[0];
    if body.proposition.to_string() != expected_body.to_string() {
        return Err("existential theorem conclusion WD changed its body fact".into());
    }
    validate_atomic_fact_well_definedness_proof_result(
        body.well_definedness.as_ref(),
        &body.proposition,
    )?;
    validate_success_store_fact_result_allowing_well_definedness_inferred_children(
        &body.store,
        &body.proposition,
        "existential theorem conclusion body WD",
    )?;
    Ok(())
}

/// Validate a universal proposition retained as a premise of a named theorem.
///
/// The named theorem compiler already renders universal premises as ordinary
/// Lean hypotheses.  The missing trust check was structural: the recursive WD
/// Result must retain the exact binder, parameter premises, domain premises,
/// conclusions, and local stores from the source proposition.  Keeping this
/// validation generic lets analysis interfaces accept pointwise hypotheses
/// without adding a theorem-specific completeness path.
fn validate_nested_forall_fact_well_definedness(
    result: &SuccessVerifyFactWellDefinedProofResult,
    expected_forall: &ForallFact,
) -> Result<(), String> {
    let SuccessVerifyFactWellDefinedProofResult::ForallFact(result) = result else {
        return Err("universal theorem premise has no universal WD Result".into());
    };
    if result.statement.to_string() != expected_forall.to_string()
        || result.binder.parameter_groups.len() != expected_forall.typed_parameters.groups.len()
        || result.premises.len() != expected_forall.dom_facts.len()
        || result.conclusions.len() != expected_forall.then_facts.len()
    {
        return Err("universal theorem premise WD changed its source structure".into());
    }

    for (group_index, (actual_group, expected_group)) in result
        .binder
        .parameter_groups
        .iter()
        .zip(expected_forall.typed_parameters.groups.iter())
        .enumerate()
    {
        if actual_group.group_index != group_index
            || actual_group.parameter_type.to_string() != expected_group.param_type.to_string()
            || actual_group.parameters.len() != expected_group.params.len()
        {
            return Err(format!(
                "universal theorem premise WD changed binder group {group_index}"
            ));
        }
        for (parameter_index, (actual_parameter, expected_parameter)) in actual_group
            .parameters
            .iter()
            .zip(expected_group.params.iter())
            .enumerate()
        {
            if actual_parameter.symbol_id != Some(expected_parameter.id()) {
                return Err(format!(
                    "universal theorem premise WD changed binder SymbolId at group {group_index}, parameter {parameter_index}"
                ));
            }
            match &expected_group.param_type {
                ParamType::Set(_) => {
                    validate_set_parameter_premise(
                        expected_parameter.id(),
                        &actual_parameter.proposition,
                    )?;
                }
                ParamType::Obj(expected_set) => {
                    validate_object_parameter_premise(
                        expected_parameter.id(),
                        expected_set,
                        &actual_parameter.proposition,
                    )?;
                }
                ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(
                        "universal theorem premise uses an unsupported refined-set binder".into(),
                    );
                }
            }
            validate_atomic_fact_well_definedness_result(
                actual_parameter.well_definedness.as_ref(),
                &actual_parameter.proposition,
            )?;
            validate_single_fact_store_output_allowing_supported_typed_inferences(
                &actual_parameter.infers,
                &actual_parameter.proposition,
                "universal theorem premise binder WD",
            )?;
        }
    }

    for (child_index, (actual, expected)) in result
        .premises
        .iter()
        .zip(expected_forall.dom_facts.iter())
        .enumerate()
    {
        if actual.proposition.to_string() != expected.to_string() {
            return Err(format!(
                "universal theorem premise WD changed domain child {child_index}"
            ));
        }
        validate_direct_named_theorem_conclusion_well_definedness(
            actual.well_definedness.as_ref(),
            &actual.proposition,
        )?;
        validate_success_store_fact_result_allowing_well_definedness_inferred_children(
            &actual.store,
            &actual.proposition,
            "universal theorem premise domain WD",
        )?;
    }
    for (child_index, (actual, expected)) in result
        .conclusions
        .iter()
        .zip(expected_forall.then_facts.iter())
        .enumerate()
    {
        let expected = expected.clone().to_fact();
        if actual.proposition.to_string() != expected.to_string() {
            return Err(format!(
                "universal theorem premise WD changed conclusion child {child_index}"
            ));
        }
        validate_direct_named_theorem_conclusion_well_definedness(
            actual.well_definedness.as_ref(),
            &actual.proposition,
        )?;
        validate_success_store_fact_result_allowing_well_definedness_inferred_children(
            &actual.store,
            &actual.proposition,
            "universal theorem premise conclusion WD",
        )?;
    }
    Ok(())
}

pub(in super::super) fn validate_atomic_fact_well_definedness_result(
    result: &SuccessVerifyFactWellDefinedResult,
    source_fact: &Fact,
) -> Result<(), String> {
    let Some(recursive) = result.recursive.as_deref() else {
        return Err("atomic fact has no atomic well-definedness result".into());
    };
    validate_atomic_fact_well_definedness_proof_result(recursive, source_fact)
}

pub(in super::super) fn validate_chain_fact_well_definedness_result(
    result: &SuccessVerifyFactWellDefinedResult,
    source_chain: &ChainFact,
    adjacent_facts: &[Fact],
) -> Result<(), String> {
    let Some(SuccessVerifyFactWellDefinedProofResult::ChainFact(chain_result)) =
        result.recursive.as_deref()
    else {
        return Err("registered transitive chain has no chain well-definedness Result".into());
    };
    if chain_result.statement.to_string() != source_chain.to_string()
        || chain_result.comparisons.len() != adjacent_facts.len()
    {
        return Err(
            "registered transitive chain well-definedness changed its source or edge arity".into(),
        );
    }
    for (index, (comparison, expected_fact)) in chain_result
        .comparisons
        .iter()
        .zip(adjacent_facts.iter())
        .enumerate()
    {
        validate_atomic_fact_well_definedness_proof_result(comparison, expected_fact)
            .map_err(|error| format!("registered transitive chain edge {index} WD: {error}"))?;
    }
    Ok(())
}

pub(in super::super) fn validate_atomic_fact_well_definedness_proof_result(
    result: &SuccessVerifyFactWellDefinedProofResult,
    source_fact: &Fact,
) -> Result<(), String> {
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) = result else {
        return Err("atomic fact has no atomic well-definedness result".into());
    };
    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("atomic fact WD validator received a non-atomic fact".into());
    };
    if atomic.statement.to_string() != source_fact.to_string() {
        return Err("atomic fact WD result changed its statement".into());
    }
    let expected_arguments = source_atomic_fact.args_ref();
    if atomic.predicate.expected_arity != expected_arguments.len()
        || atomic.arguments.len() != expected_arguments.len()
    {
        return Err("atomic fact WD result changed its predicate arity".into());
    }
    let mut visited = HashSet::new();
    for (expected_index, expected_object) in expected_arguments.into_iter().enumerate() {
        let argument = atomic
            .arguments
            .iter()
            .find(|argument| argument.argument_index == expected_index)
            .ok_or_else(|| format!("closed membership WD result lost argument {expected_index}"))?;
        if obj_equality_key(&argument.source_object) != obj_equality_key(expected_object) {
            return Err(format!(
                "closed membership WD argument {expected_index} changed its source object"
            ));
        }
        validate_success_obj_well_defined_result(
            argument.result.as_ref(),
            expected_object,
            &mut visited,
        )?;
    }
    Ok(())
}

pub(in super::super) fn fact_result_contains_inferred_facts(
    result: &SuccessFactStmtResult,
) -> bool {
    !result.store.infers.rule_applications.is_empty()
        || result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
}

pub(in super::super) fn direct_forall_result_publication_selections(
    result: &SuccessFactStmtResult,
    source_forall: &ForallFact,
) -> Result<Vec<DirectForallResultPublicationSelection>, String> {
    if result.store.fact.to_string() != Fact::from(source_forall.clone()).to_string() {
        return Err("ForallProof store changed its source proposition".into());
    }
    if !result.store.infers.rule_applications.is_empty() {
        return Err(
            "ForallProof store mixed theorem publication with typed inference rules".into(),
        );
    }
    if result
        .store
        .infers
        .store_fact_outputs
        .iter()
        .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
    {
        return Err(
            "ForallProof projection publication must use exact top-level store outputs".into(),
        );
    }

    let source_fact: Fact = source_forall.clone().into();
    let source_parameters = source_forall
        .typed_parameters
        .collect_param_bindings_with_types();
    let SuccessFactProofResult::ForallProof(proof) = result.proof() else {
        return Err("direct forall publication retained another proof family".into());
    };
    if proof.proves.len() != source_forall.then_facts.len() {
        return Err("direct forall publication changed its conclusion Result arity".into());
    }
    let Some(SuccessVerifyFactWellDefinedProofResult::ForallFact(forall_wd)) =
        result.well_definedness.recursive.as_deref()
    else {
        return Err("direct forall publication retained no forall WD Result".into());
    };
    if forall_wd.conclusions.len() != source_forall.then_facts.len() {
        return Err("direct forall publication changed its WD conclusion arity".into());
    }

    fn push_available_conclusion(
        available: &mut Vec<(usize, FactId, Fact, u8)>,
        owner: usize,
        fact_id: FactId,
        fact: Fact,
        rank: u8,
    ) {
        if !available
            .iter()
            .any(|(existing_owner, existing_id, existing_fact, _)| {
                *existing_owner == owner
                    && *existing_id == fact_id
                    && existing_fact.to_string() == fact.to_string()
            })
        {
            available.push((owner, fact_id, fact, rank));
        }
    }

    fn collect_infer_candidates(
        infers: &SuccessInferResult,
        owner: usize,
        rank: u8,
        available: &mut Vec<(usize, FactId, Fact, u8)>,
    ) -> Result<(), String> {
        for output in &infers.store_fact_outputs {
            if let Some(fact_id) = output.fact_id {
                push_available_conclusion(
                    available,
                    owner,
                    fact_id,
                    output.itself_and_why_itself_is_stored.0.clone(),
                    rank,
                );
            }
            if output.inferred_facts.len() != output.inferred_fact_ids.len() {
                return Err(format!(
                    "ForallProof conclusion {owner} changed its inferred FactId arity"
                ));
            }
            for (fact, fact_id) in output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
            {
                let fact_id = fact_id.ok_or_else(|| {
                    format!("ForallProof conclusion {owner} inferred `{fact}` without a FactId")
                })?;
                push_available_conclusion(available, owner, fact_id, fact.clone(), rank);
            }
        }
        for application in &infers.rule_applications {
            for premise in &application.premises {
                if let Some(fact_id) = premise.fact_id {
                    push_available_conclusion(
                        available,
                        owner,
                        fact_id,
                        premise.fact.clone(),
                        rank,
                    );
                }
            }
            for conclusion in &application.conclusions {
                if let Some(fact_id) = conclusion.fact_id {
                    push_available_conclusion(
                        available,
                        owner,
                        fact_id,
                        conclusion.fact.clone(),
                        rank,
                    );
                }
                collect_infer_candidates(&conclusion.infers, owner, rank, available)?;
            }
        }
        Ok(())
    }

    fn collect_child_fact_candidates(
        child: &SuccessFactStmtResult,
        owner: usize,
        available: &mut Vec<(usize, FactId, Fact, u8)>,
    ) -> Result<(), String> {
        if let Some(fact_id) = child.store.fact_id {
            push_available_conclusion(available, owner, fact_id, child.fact(), 1);
        }
        collect_infer_candidates(&child.store.infers, owner, 1, available)?;
        if let SuccessFactProofResult::CombinedProofs(combined) = child.proof() {
            for step in &combined.steps {
                if let Some(factual) = step.factual_success() {
                    collect_child_fact_candidates(factual, owner, available)?;
                }
            }
        }
        Ok(())
    }

    let mut available_conclusions = Vec::new();
    let mut source_primary_fact_ids = Vec::with_capacity(source_forall.then_facts.len());
    for (source_index, (source_conclusion, proved)) in source_forall
        .then_facts
        .iter()
        .zip(proof.proves.iter())
        .enumerate()
    {
        let child = proved
            .result
            .factual_success()
            .ok_or_else(|| format!("ForallProof conclusion {source_index} is not factual"))?;
        let source_fact = source_conclusion.clone().to_fact();
        if child.fact().to_string() != source_fact.to_string()
            || child.store.fact.to_string() != source_fact.to_string()
        {
            return Err(format!(
                "ForallProof conclusion {source_index} changed its target before publication"
            ));
        }
        let primary_fact_id = child
            .store
            .fact_id
            .ok_or_else(|| format!("ForallProof conclusion {source_index} has no frozen FactId"))?;
        source_primary_fact_ids.push(primary_fact_id);
        push_available_conclusion(
            &mut available_conclusions,
            source_index,
            primary_fact_id,
            source_fact,
            0,
        );
        collect_child_fact_candidates(child, source_index, &mut available_conclusions)?;
        let wd_store = &forall_wd.conclusions[source_index].store;
        if let Some(fact_id) = wd_store.fact_id {
            push_available_conclusion(
                &mut available_conclusions,
                source_index,
                fact_id,
                wd_store.fact.clone(),
                2,
            );
        }
        collect_infer_candidates(
            &wd_store.infers,
            source_index,
            2,
            &mut available_conclusions,
        )?;
    }

    let select_published_conclusions = |projected: &ForallFact| {
        let mut selected = Vec::with_capacity(projected.then_facts.len());
        let mut used_fact_ids = HashSet::new();
        for projected_conclusion in &projected.then_facts {
            let projected_fact = projected_conclusion.clone().to_fact();
            let matching_rank = available_conclusions
                .iter()
                .filter(|(_, fact_id, fact, _)| {
                    !used_fact_ids.contains(fact_id)
                        && fact.to_string() == projected_fact.to_string()
                })
                .map(|(_, _, _, rank)| *rank)
                .min();
            let matching_owner = available_conclusions
                .iter()
                .filter(|(_, fact_id, fact, rank)| {
                    Some(*rank) == matching_rank
                        && !used_fact_ids.contains(fact_id)
                        && fact.to_string() == projected_fact.to_string()
                })
                .map(|(owner, _, _, _)| *owner)
                .min();
            let matches = available_conclusions
                .iter()
                .filter(|(owner, fact_id, fact, rank)| {
                    Some(*rank) == matching_rank
                        && Some(*owner) == matching_owner
                        && !used_fact_ids.contains(fact_id)
                        && fact.to_string() == projected_fact.to_string()
                })
                .cloned()
                .collect::<Vec<_>>();
            let [selected_conclusion] = matches.as_slice() else {
                return Err(format!(
                    "stored ForallProof conclusion `{projected_fact}` has {} exact child-Result owners",
                    matches.len()
                ));
            };
            used_fact_ids.insert(selected_conclusion.1);
            selected.push((
                selected_conclusion.0,
                selected_conclusion.1,
                selected_conclusion.2.clone(),
            ));
        }
        Ok::<_, String>(selected)
    };

    if let Some(stored_fact_id) = result.store.fact_id {
        let matching_outputs = result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .filter(|output| {
                output.fact_id == Some(stored_fact_id)
                    && output.itself_and_why_itself_is_stored.0.to_string()
                        == source_fact.to_string()
            })
            .count();
        if matching_outputs != 1 || result.store.infers.store_fact_outputs.len() != 1 {
            return Err(
                "stored ForallProof did not retain exactly one matching source store output".into(),
            );
        }
        return Ok(vec![DirectForallResultPublicationSelection {
            forall_fact: source_forall.clone(),
            stored_fact_id: Some(stored_fact_id),
            source_parameter_indices: (0..source_parameters.len()).collect(),
            source_conclusion_indices: (0..source_forall.then_facts.len()).collect(),
            published_conclusions: select_published_conclusions(source_forall)?,
        }]);
    }

    let mut saw_transient_source = false;
    let mut selections = Vec::new();
    let mut selected_source_primary_conclusions = HashSet::new();
    for output in &result.store.infers.store_fact_outputs {
        let proposition = &output.itself_and_why_itself_is_stored.0;
        if proposition.to_string() == source_fact.to_string() {
            if output.fact_id.is_some() || saw_transient_source {
                return Err(
                    "unstored ForallProof retained an invalid or duplicate source store output"
                        .into(),
                );
            }
            saw_transient_source = true;
            continue;
        }

        let Fact::ForallFact(projected) = proposition else {
            return Err(format!(
                "ForallProof store published a non-forall side effect `{proposition}`"
            ));
        };
        let stored_fact_id = output.fact_id.ok_or_else(|| {
            "stored ForallProof projection reached the compiler without a FactId".to_string()
        })?;
        if projected
            .dom_facts
            .iter()
            .map(ToString::to_string)
            .ne(source_forall.dom_facts.iter().map(ToString::to_string))
        {
            return Err("stored ForallProof projection changed its domain premises".into());
        }

        let projected_parameters = projected
            .typed_parameters
            .collect_param_bindings_with_types();
        let mut source_parameter_indices = Vec::with_capacity(projected_parameters.len());
        let mut last_source_parameter_index = None;
        for (projected_binding, projected_type) in projected_parameters {
            let Some((source_index, (_, source_type))) = source_parameters
                .iter()
                .enumerate()
                .find(|(_, (source_binding, _))| source_binding.id() == projected_binding.id())
            else {
                return Err("stored ForallProof projection introduced a new binder".into());
            };
            if last_source_parameter_index.is_some_and(|last| source_index <= last)
                || !direct_forall_parameter_types_match_for_projection(source_type, &projected_type)
            {
                return Err(
                    "stored ForallProof projection changed binder order or parameter type".into(),
                );
            }
            source_parameter_indices.push(source_index);
            last_source_parameter_index = Some(source_index);
        }

        if projected.then_facts.is_empty() {
            return Err("stored ForallProof projection has no conclusion".into());
        }
        let published_conclusions = select_published_conclusions(projected)?;
        let mut source_conclusion_indices = published_conclusions
            .iter()
            .map(|(source_index, _, _)| *source_index)
            .collect::<Vec<_>>();
        source_conclusion_indices.sort_unstable();
        source_conclusion_indices.dedup();
        for (source_index, fact_id, _) in &published_conclusions {
            if *fact_id == source_primary_fact_ids[*source_index]
                && !selected_source_primary_conclusions.insert(*source_index)
            {
                return Err("stored ForallProof projections duplicated a source conclusion".into());
            }
        }
        selections.push(DirectForallResultPublicationSelection {
            forall_fact: projected.clone(),
            stored_fact_id: Some(stored_fact_id),
            source_parameter_indices,
            source_conclusion_indices,
            published_conclusions,
        });
    }

    if !saw_transient_source {
        return Err("unstored ForallProof lost its transient source store output".into());
    }
    if selections.is_empty() {
        if result.store.infers.store_fact_outputs.len() != 1 {
            return Err("unstored ForallProof retained unexplained store outputs".into());
        }
        return Ok(vec![DirectForallResultPublicationSelection {
            forall_fact: source_forall.clone(),
            stored_fact_id: None,
            source_parameter_indices: (0..source_parameters.len()).collect(),
            source_conclusion_indices: (0..source_forall.then_facts.len()).collect(),
            published_conclusions: select_published_conclusions(source_forall)?,
        }]);
    }
    if selected_source_primary_conclusions.len() != source_forall.then_facts.len() {
        return Err(
            "stored ForallProof projections did not publish every source conclusion".into(),
        );
    }
    selections.sort_by_key(|selection| {
        selection
            .source_conclusion_indices
            .first()
            .copied()
            .unwrap_or(usize::MAX)
    });
    Ok(selections)
}

pub(in super::super) fn direct_forall_parameter_types_match_for_projection(
    source: &ParamType,
    projected: &ParamType,
) -> bool {
    match (source, projected) {
        (ParamType::Set(_), ParamType::Set(_))
        | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
        | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => true,
        (ParamType::Obj(source), ParamType::Obj(projected)) => {
            obj_equality_key(source) == obj_equality_key(projected)
        }
        _ => false,
    }
}
