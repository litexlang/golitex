use super::*;

pub(super) fn compile_standard_set_nonempty_fact_proof_from_result(
    result: &StmtResult,
    expected_carrier: &Obj,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let success = result
        .factual_success()
        .ok_or_else(|| "object choice nonemptiness child is not a successful fact".to_string())?;
    let target = success.fact();
    let Fact::AtomicFact(AtomicFact::IsNonemptySetFact(nonempty)) = &target else {
        return Err("object choice nonemptiness child changed fact family".into());
    };
    if obj_equality_key(&nonempty.set) != obj_equality_key(expected_carrier)
        || success.store.fact.to_string() != target.to_string()
        || success.store.fact_id.is_some()
        || !success.store.infers.is_empty()
    {
        return Err(
            "object choice nonemptiness child changed its target or verify-only store".into(),
        );
    }
    let SuccessFactProofResult::BuiltinRule(builtin) = success.proof() else {
        return Err("object choice nonemptiness child is not a builtin leaf".into());
    };
    let Some(BuiltinRuleEvidence::StandardSetNonempty(evidence)) = builtin.evidence.typed() else {
        return Err("object choice nonemptiness child has no typed standard-set evidence".into());
    };
    let Obj::StandardSet(target_set) = expected_carrier else {
        return Err("object choice direct compiler currently requires a standard carrier".into());
    };
    if !builtin.subgoals.is_empty()
        || evidence.expected_target.to_string() != target.to_string()
        || evidence.target_set != *target_set
    {
        return Err("standard-set nonempty evidence changed its target or children".into());
    }
    let theorem = match target_set {
        StandardSet::N => "Litex.Rules.naturalNonempty",
        StandardSet::Z => "Litex.Rules.integerNonempty",
        StandardSet::Q => "Litex.Rules.rationalNonempty",
        StandardSet::R => "Litex.Rules.realNonempty",
        StandardSet::C => "Litex.Rules.complexNonempty",
        unsupported => {
            return Err(format!(
                "unsupported direct standard-set nonempty carrier `{unsupported}`"
            ));
        }
    };
    let rendered_target = render_fact(&target, environment_stack)?;
    let rendered_carrier = render_obj(expected_carrier, environment_stack)?;
    if rendered_target != format!("Litex.Set.Nonempty {rendered_carrier}") {
        return Err("standard-set nonempty evidence changed its rendered target".into());
    }
    Ok(theorem.into())
}

pub(super) fn object_type_fact_for_compiler_definition(
    object: Obj,
    param_type: &ParamType,
    line_file: LineFile,
) -> Fact {
    match param_type {
        ParamType::Set(_) => IsSetFact::new(object, line_file).into(),
        ParamType::NonemptySet(_) => IsNonemptySetFact::new(object, line_file).into(),
        ParamType::FiniteSet(_) => IsFiniteSetFact::new(object, line_file).into(),
        ParamType::Obj(set) => InFact::new(object, set.clone(), line_file).into(),
    }
}

pub(super) fn exact_ordered_fact_ids_from_store_results(
    infer_result: &SuccessInferResult,
    expected_facts: &[Fact],
    statement_family: &str,
) -> Result<Vec<FactId>, String> {
    if infer_result.store_fact_outputs.len() != expected_facts.len() {
        return Err(format!(
            "{statement_family} stored {} facts but its Result requires {}",
            infer_result.store_fact_outputs.len(),
            expected_facts.len()
        ));
    }
    infer_result
        .store_fact_outputs
        .iter()
        .zip(expected_facts.iter())
        .enumerate()
        .map(|(index, (stored, expected))| {
            if stored.itself_and_why_itself_is_stored.0.to_string() != expected.to_string() {
                return Err(format!(
                    "{statement_family} store {index} changed `{expected}` to `{}`",
                    stored.itself_and_why_itself_is_stored.0
                ));
            }
            stored.fact_id.ok_or_else(|| {
                format!("{statement_family} store {index} for `{expected}` has no FactId")
            })
        })
        .collect()
}

pub(super) fn infer_result_retains_fact_id(
    infer_result: &SuccessInferResult,
    expected_fact: &Fact,
    expected_fact_id: FactId,
) -> bool {
    infer_result.store_fact_outputs.iter().any(|output| {
        (output.fact_id == Some(expected_fact_id)
            && output.itself_and_why_itself_is_stored.0.to_string() == expected_fact.to_string())
            || output
                .inferred_facts
                .iter()
                .zip(output.inferred_fact_ids.iter())
                .any(|(fact, fact_id)| {
                    fact.to_string() == expected_fact.to_string()
                        && *fact_id == Some(expected_fact_id)
                })
    })
}

pub(super) fn defined_predicate_infer_rule(rule: &InferRule) -> bool {
    matches!(
        rule,
        InferRule::DefinedPredicateParameterRequirementProjection(_)
            | InferRule::DefinedPredicateDefinitionClauseProjection(_)
    )
}

pub(super) fn infer_rule_name(rule: &InferRule) -> &'static str {
    match rule {
        InferRule::NaturalMembershipImpliesNonnegative => "NaturalMembershipImpliesNonnegative",
        InferRule::PositiveStandardSetMembershipImpliesPositive(_) => {
            "PositiveStandardSetMembershipImpliesPositive"
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(_) => {
            "NegativeStandardSetMembershipImpliesNegative"
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(_) => {
            "NonzeroStandardSetMembershipImpliesNonzero"
        }
        InferRule::SetBuilderBaseMembershipProjection => "SetBuilderBaseMembershipProjection",
        InferRule::SetBuilderPredicateProjection { .. } => "SetBuilderPredicateProjection",
        InferRule::DefinedPredicateParameterRequirementProjection(_) => {
            "DefinedPredicateParameterRequirementProjection"
        }
        InferRule::DefinedPredicateDefinitionClauseProjection(_) => {
            "DefinedPredicateDefinitionClauseProjection"
        }
        InferRule::RegisteredTransitivePredicateChainClosure(_) => {
            "RegisteredTransitivePredicateChainClosure"
        }
        InferRule::TupleEqualityWithKnownTupleImpliesTupleShape(_) => {
            "TupleEqualityWithKnownTupleImpliesTupleShape"
        }
        InferRule::ListSetMembershipImpliesEqualityAlternatives(_) => {
            "ListSetMembershipImpliesEqualityAlternatives"
        }
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            "MultiplicationByNegativeOneReversesOrderAgainstZero"
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            "StrictOrderComparedToZeroImpliesWeakOrder"
        }
        InferRule::MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet(_) => {
            "MembershipInSetWithKnownEqualityImpliesMembershipInEqualSet"
        }
        InferRule::SubsetImpliesElementwiseMembershipForall(_) => {
            "SubsetImpliesElementwiseMembershipForall"
        }
        InferRule::SupersetImpliesElementwiseMembershipForall(_) => {
            "SupersetImpliesElementwiseMembershipForall"
        }
        InferRule::ConjunctionImpliesComponent(_) => "ConjunctionImpliesComponent",
    }
}

pub(super) fn validate_flattened_inferred_fact_ids_are_visible(
    infer_result: &SuccessInferResult,
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
    result_layer: &str,
) -> Result<(), String> {
    for (store_index, output) in infer_result.store_fact_outputs.iter().enumerate() {
        let fact_id = output
            .fact_id
            .ok_or_else(|| format!("{result_layer} store {store_index} has no frozen FactId"))?;
        resolve_fact_citation(
            &fact_id,
            &output.itself_and_why_itself_is_stored.0,
            environment_stack,
        )?;
        if output.inferred_facts.len() != output.inferred_fact_ids.len() {
            return Err(format!(
                "{result_layer} store {store_index} changed its inferred FactId arity"
            ));
        }
        for (inferred_index, (fact, fact_id)) in output
            .inferred_facts
            .iter()
            .zip(output.inferred_fact_ids.iter())
            .enumerate()
        {
            let fact_id = fact_id.ok_or_else(|| {
                format!(
                    "{result_layer} store {store_index} inferred fact {inferred_index} has no frozen FactId"
                )
            })?;
            resolve_fact_citation(&fact_id, fact, environment_stack)?;
        }
    }
    Ok(())
}

pub(super) fn success_infer_results_have_same_semantic_structure(
    left: &SuccessInferResult,
    right: &SuccessInferResult,
) -> bool {
    left.store_fact_outputs.len() == right.store_fact_outputs.len()
        && left
            .store_fact_outputs
            .iter()
            .zip(right.store_fact_outputs.iter())
            .all(|(left, right)| {
                left.fact_id == right.fact_id
                    && left.itself_and_why_itself_is_stored.0.to_string()
                        == right.itself_and_why_itself_is_stored.0.to_string()
                    && left.itself_and_why_itself_is_stored.1
                        == right.itself_and_why_itself_is_stored.1
                    && left.inferred_fact_ids == right.inferred_fact_ids
                    && left.inferred_facts.len() == right.inferred_facts.len()
                    && left
                        .inferred_facts
                        .iter()
                        .zip(right.inferred_facts.iter())
                        .all(|(left, right)| left.to_string() == right.to_string())
            })
        && left.rule_applications.len() == right.rule_applications.len()
        && left
            .rule_applications
            .iter()
            .zip(right.rule_applications.iter())
            .all(|(left, right)| {
                left.rule == right.rule
                    && left.premises.len() == right.premises.len()
                    && left
                        .premises
                        .iter()
                        .zip(right.premises.iter())
                        .all(|(left, right)| {
                            left.fact_id == right.fact_id
                                && left.fact.to_string() == right.fact.to_string()
                        })
                    && left.conclusions.len() == right.conclusions.len()
                    && left
                        .conclusions
                        .iter()
                        .zip(right.conclusions.iter())
                        .all(|(left, right)| {
                            left.fact_id == right.fact_id
                                && left.fact.to_string() == right.fact.to_string()
                                && success_infer_results_have_same_semantic_structure(
                                    &left.infers,
                                    &right.infers,
                                )
                        })
            })
}

pub(super) fn equality_transport_has_no_steps(
    transport: Option<&EqualityTransportEvidence>,
) -> bool {
    transport.is_none_or(|transport| transport.steps.is_empty())
}

pub(super) fn atomic_fact_is_logically_negated(fact: &AtomicFact) -> bool {
    matches!(
        fact,
        AtomicFact::NotNormalAtomicFact(_)
            | AtomicFact::NotEqualFact(_)
            | AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::NotIsSetFact(_)
            | AtomicFact::NotIsNonemptySetFact(_)
            | AtomicFact::NotIsFiniteSetFact(_)
            | AtomicFact::NotInFact(_)
            | AtomicFact::NotIsCartFact(_)
            | AtomicFact::NotIsTupleFact(_)
            | AtomicFact::NotSubsetFact(_)
            | AtomicFact::NotSupersetFact(_)
    )
}

pub(super) fn validate_compiled_fact_proof_effects(
    infer_result: &SuccessInferResult,
    proofs: &[CompiledFactProofBody],
    environment_stack: &StmtResultToLeanCompilerEnvironmentStack,
    result_layer: &str,
) -> Result<Vec<Option<FactId>>, String> {
    if !infer_result.rule_applications.is_empty() {
        return Err(format!(
            "{result_layer} unexpectedly retained typed inference rules"
        ));
    }
    for output in &infer_result.store_fact_outputs {
        if !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty() {
            return Err(format!(
                "{result_layer} retained inferred children beside its direct outputs"
            ));
        }
    }

    let mut output_index = 0;
    let mut fact_ids = Vec::with_capacity(proofs.len());
    for proof in proofs {
        let next_output = infer_result.store_fact_outputs.get(output_index);
        if next_output.is_some_and(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == proof.fact.to_string()
        }) {
            let output = next_output.expect("checked as present");
            fact_ids.push(Some(output.fact_id.ok_or_else(|| {
                format!("{result_layer} store {output_index} has no FactId")
            })?));
            output_index += 1;
            continue;
        }

        let fact_was_already_visible = environment_stack
            .fact_propositions
            .values()
            .any(|visible| visible.to_string() == proof.fact.to_string());
        if !fact_was_already_visible {
            return Err(format!(
                "{result_layer} neither stored `{}` nor reused it from the current compiler environment",
                proof.fact
            ));
        }
        fact_ids.push(None);
    }
    if output_index != infer_result.store_fact_outputs.len() {
        return Err(format!(
            "{result_layer} retained a store output that does not match its ordered facts"
        ));
    }
    Ok(fact_ids)
}

pub(super) fn validate_generated_fact_publication_effects(
    infers: &SuccessInferResult,
    expected: &Fact,
    result_layer: &str,
) -> Result<FactId, String> {
    if !infers.rule_applications.is_empty() || infers.store_fact_outputs.is_empty() {
        return Err(format!(
            "{result_layer} must retain only its generated-fact stores"
        ));
    }
    let mut exact_fact_id = None;
    for (store_index, store) in infers.store_fact_outputs.iter().enumerate() {
        if store.itself_and_why_itself_is_stored.0.to_string() != expected.to_string()
            || !store.inferred_facts.is_empty()
            || !store.inferred_fact_ids.is_empty()
        {
            return Err(format!(
                "{result_layer} store {store_index} changed its generated fact or retained inferred children"
            ));
        }
        let fact_id = store
            .fact_id
            .ok_or_else(|| format!("{result_layer} store {store_index} has no FactId"))?;
        if exact_fact_id.is_some_and(|retained| retained != fact_id) {
            return Err(format!(
                "{result_layer} assigned multiple FactIds to one generated fact"
            ));
        }
        exact_fact_id = Some(fact_id);
    }
    exact_fact_id.ok_or_else(|| format!("{result_layer} retained no FactId"))
}

pub(super) fn render_forall_domain_intro_suffix(forall: &ForallFact) -> String {
    (1..=forall.dom_facts.len())
        .map(|index| format!(" __domain{index}"))
        .collect::<String>()
}

pub(super) fn obj_from_closed_or_half_open_range(range: &ClosedRangeOrRange) -> Obj {
    match range {
        ClosedRangeOrRange::Range(range) => range.clone().into(),
        ClosedRangeOrRange::ClosedRange(range) => range.clone().into(),
    }
}

pub(super) fn closed_or_half_open_range_endpoints(range: &ClosedRangeOrRange) -> (&Obj, &Obj) {
    match range {
        ClosedRangeOrRange::Range(range) => (range.start.as_ref(), range.end.as_ref()),
        ClosedRangeOrRange::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref()),
    }
}

pub(super) fn literal_integer_values_for_range(
    range: &ClosedRangeOrRange,
) -> Result<Option<Vec<String>>, String> {
    let (start, end) = closed_or_half_open_range_endpoints(range);
    let (Obj::Number(start), Obj::Number(end)) = (start, end) else {
        return Ok(None);
    };
    let start = start
        .normalized_value
        .parse::<i128>()
        .map_err(|_| "integer-range start is not a literal integer".to_string())?;
    let end = end
        .normalized_value
        .parse::<i128>()
        .map_err(|_| "integer-range end is not a literal integer".to_string())?;
    let closed = matches!(range, ClosedRangeOrRange::ClosedRange(_));
    if (closed && start > end) || (!closed && start >= end) {
        return Ok(Some(Vec::new()));
    }
    let final_value = if closed {
        end
    } else {
        end.checked_sub(1)
            .ok_or_else(|| "half-open integer-range boundary underflowed i128".to_string())?
    };
    let mut values = Vec::new();
    let mut current = start;
    loop {
        values.push(current.to_string());
        if current == final_value {
            break;
        }
        current = current
            .checked_add(1)
            .ok_or_else(|| "integer-range enumeration overflowed i128".to_string())?;
    }
    Ok(Some(values))
}

pub(super) fn validate_by_for_range_parameter_result(
    result: &SuccessVerifyByForRangeParameterResult,
) -> Result<(), String> {
    let (source_start, source_end, closed) = match &result.range {
        ClosedRangeOrRange::Range(range) => (range.start.as_ref(), range.end.as_ref(), false),
        ClosedRangeOrRange::ClosedRange(range) => (range.start.as_ref(), range.end.as_ref(), true),
    };
    let expected_start = LeanTargetObjectRepresentation::Number {
        normalized_value: result.evaluated_start.clone(),
    };
    let expected_end = LeanTargetObjectRepresentation::Number {
        normalized_value: result.evaluated_end.clone(),
    };
    if LeanTargetObjectRepresentation::lower(source_start)? != expected_start
        || LeanTargetObjectRepresentation::lower(source_end)? != expected_end
    {
        return Err(format!(
            "by-for parameter `{}` needs retained endpoint-normalization evidence before a non-literal range may be compiled",
            result.parameter
        ));
    }
    let start = result
        .evaluated_start
        .parse::<i128>()
        .map_err(|_| "by-for evaluated start is not an integer".to_string())?;
    let end = result
        .evaluated_end
        .parse::<i128>()
        .map_err(|_| "by-for evaluated end is not an integer".to_string())?;
    let is_empty = if closed { start > end } else { start >= end };
    if is_empty {
        if result.enumerated_values.is_empty() {
            return Ok(());
        }
        return Err("by-for empty range retained assignments".into());
    }
    let right_boundary = if closed {
        end
    } else {
        end.checked_sub(1)
            .ok_or_else(|| "by-for half-open range boundary underflowed i128".to_string())?
    };
    let mut expected_value = start;
    for retained in &result.enumerated_values {
        if retained.parse::<i128>().ok() != Some(expected_value) {
            return Err(format!(
                "by-for parameter `{}` changed its ordered evaluated values",
                result.parameter
            ));
        }
        if expected_value == right_boundary {
            break;
        }
        expected_value = expected_value
            .checked_add(1)
            .ok_or_else(|| "by-for evaluated range overflowed i128".to_string())?;
    }
    if result
        .enumerated_values
        .last()
        .and_then(|value| value.parse::<i128>().ok())
        != Some(right_boundary)
    {
        return Err(format!(
            "by-for parameter `{}` lost one or more evaluated values",
            result.parameter
        ));
    }
    Ok(())
}

pub(super) fn validate_single_fact_store_output(
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

pub(super) fn validate_conjunction_store_and_component_inference_results(
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

pub(super) fn validate_success_store_fact_result(
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
pub(super) fn validate_success_store_fact_result_allowing_well_definedness_inferred_children(
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
    if store
        .infers
        .rule_applications
        .iter()
        .any(|application| !defined_predicate_infer_rule(&application.rule))
    {
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

fn validate_conjunction_well_definedness_preflight_store(
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

fn collect_infer_result_fact_identities(
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

pub(super) fn validate_typed_infer_result_identity_completeness(
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
pub(super) fn select_typed_inference_results_for_visible_forall_sources(
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

pub(super) fn describe_success_fact_result_for_direct_compilation_audit(
    result: &SuccessFactStmtResult,
) -> String {
    let proof = match result.proof() {
        SuccessFactProofResult::BuiltinRule(proof) => format!(
            "BuiltinRule evidence={:?}, subgoals={}",
            proof.evidence,
            proof.subgoals.len()
        ),
        SuccessFactProofResult::BuiltinStrategy(proof) => format!(
            "BuiltinStrategy evidence={:?}, subgoals={}",
            proof.evidence,
            proof.subgoals.len()
        ),
        SuccessFactProofResult::StoredFactCitation(_) => "StoredFactCitation".to_string(),
        SuccessFactProofResult::Strategy(_) => "Strategy".to_string(),
        SuccessFactProofResult::KnownForallInstantiation(_) => {
            "KnownForallInstantiation".to_string()
        }
        SuccessFactProofResult::DefinitionReduction(_) => "DefinitionReduction".to_string(),
        SuccessFactProofResult::CheckedFunctionDefinitionReduction(_) => {
            "CheckedFunctionDefinitionReduction".to_string()
        }
        SuccessFactProofResult::DiagnosticOnly(_) => "DiagnosticOnly".to_string(),
        SuccessFactProofResult::CombinedProofs(proof) => {
            format!(
                "CombinedProofs primary={}, steps={}",
                proof.primary.is_some(),
                proof.steps.len()
            )
        }
        SuccessFactProofResult::ForallProof(proof) => {
            let assumption_rules = proof
                .assumption_infers
                .rule_applications
                .iter()
                .map(|application| infer_rule_name(&application.rule))
                .collect::<Vec<_>>();
            let conclusion_shapes = proof
                .proves
                .iter()
                .map(|proved| {
                    proved
                        .result
                        .factual_success()
                        .map(|result| match result.proof() {
                            SuccessFactProofResult::BuiltinRule(proof) => format!(
                                "BuiltinRule({:?}, subgoals={})",
                                proof.evidence,
                                proof.subgoals.len()
                            ),
                            SuccessFactProofResult::BuiltinStrategy(proof) => format!(
                                "BuiltinStrategy({:?}, subgoals={})",
                                proof.evidence,
                                proof.subgoals.len()
                            ),
                            SuccessFactProofResult::StoredFactCitation(_) => {
                                "StoredFactCitation".to_string()
                            }
                            SuccessFactProofResult::Strategy(_) => "Strategy".to_string(),
                            SuccessFactProofResult::KnownForallInstantiation(_) => {
                                "KnownForallInstantiation".to_string()
                            }
                            SuccessFactProofResult::DefinitionReduction(_) => {
                                "DefinitionReduction".to_string()
                            }
                            SuccessFactProofResult::CheckedFunctionDefinitionReduction(_) => {
                                "CheckedFunctionDefinitionReduction".to_string()
                            }
                            SuccessFactProofResult::DiagnosticOnly(_) => {
                                "DiagnosticOnly".to_string()
                            }
                            SuccessFactProofResult::CombinedProofs(proof) => {
                                format!(
                                    "CombinedProofs(primary={}, steps={})",
                                    proof.primary.is_some(),
                                    proof.steps.len()
                                )
                            }
                            SuccessFactProofResult::ForallProof(_) => {
                                "NestedForallProof".to_string()
                            }
                            SuccessFactProofResult::Transform(_) => "Transform".to_string(),
                            SuccessFactProofResult::Reuse(_) => "Reuse".to_string(),
                        })
                        .unwrap_or_else(|| "NonFactual".to_string())
                })
                .collect::<Vec<_>>();
            format!(
                "ForallProof parameter_stores={}, assumption_rules={assumption_rules:?}, conclusions={conclusion_shapes:?}",
                proof.assumption_infers.store_fact_outputs.len(),
            )
        }
        SuccessFactProofResult::Transform(_) => "Transform".to_string(),
        SuccessFactProofResult::Reuse(_) => "Reuse".to_string(),
    };
    format!(
        "{proof}; infer_rules={}, stores={}",
        result.store.infers.rule_applications.len(),
        result.store.infers.store_fact_outputs.len()
    )
}

/// Keep direct builtin coverage compile-time exhaustive. Returning `None`
/// means the evidence has a direct Result consumer above. A named limitation
/// is an intentional fail-closed boundary, never permission to fall through
/// to the compatibility builder. Adding a new `BuiltinRuleEvidence` variant
/// therefore requires an explicit compiler decision here.
pub(super) fn direct_builtin_rule_compiler_limitation(
    evidence: &BuiltinRuleEvidence,
) -> Option<&'static str> {
    match evidence {
        BuiltinRuleEvidence::MatrixExpressionMembership(_) => Some(
            "StmtResultToLeanCompiler does not yet represent native matrix expressions in the Lean target ABI",
        ),
        BuiltinRuleEvidence::DivNotEqualZero(_) => Some(
            "StmtResultToLeanCompiler cannot yet replay division nonzero until Litex.Same has a reviewed numeric-observation elimination theorem",
        ),
        BuiltinRuleEvidence::NotEqualFromStrictOrder => Some(
            "StmtResultToLeanCompiler cannot yet replay strict-order inequality until Litex.Same has a reviewed numeric-observation elimination theorem",
        ),
        BuiltinRuleEvidence::AbsoluteValue(_) => Some(
            "StmtResultToLeanCompiler does not yet have a reviewed absolute-value representation and proof adapter in the Lean target ABI",
        ),
        BuiltinRuleEvidence::RegisteredLocal(_)
        | BuiltinRuleEvidence::DefinitionProjection(_)
        | BuiltinRuleEvidence::SetBuilderMembership(_)
        | BuiltinRuleEvidence::FunctionSetMembership(_)
        | BuiltinRuleEvidence::RefinedNumericMembership(_)
        | BuiltinRuleEvidence::ClosedNumericMembership(_)
        | BuiltinRuleEvidence::ClosedNumericNonmembership(_)
        | BuiltinRuleEvidence::ClosedNumericComparison(_)
        | BuiltinRuleEvidence::OrderReflexivity(_)
        | BuiltinRuleEvidence::RuntimeResolvedNumericComparison(_)
        | BuiltinRuleEvidence::RegisteredReflexivePredicate(_)
        | BuiltinRuleEvidence::RegisteredSymmetricPredicate(_)
        | BuiltinRuleEvidence::RegisteredAntisymmetricPredicate(_)
        | BuiltinRuleEvidence::ObjectReflexivity(_)
        | BuiltinRuleEvidence::RationalNormalization(_)
        | BuiltinRuleEvidence::ComplexAlgebraicNormalization(_)
        | BuiltinRuleEvidence::StandardSetNonempty(_)
        | BuiltinRuleEvidence::DisjunctionIntroduction(_)
        | BuiltinRuleEvidence::FunctionApplicationReturnMembership(_)
        | BuiltinRuleEvidence::KnownEqualityPath(_)
        | BuiltinRuleEvidence::Arithmetic(_)
        | BuiltinRuleEvidence::IntegerMembershipClosure(_)
        | BuiltinRuleEvidence::NaturalMembershipClosure(_)
        | BuiltinRuleEvidence::RationalMembershipClosure(_)
        | BuiltinRuleEvidence::ComplexArithmeticMembershipClosure(_)
        | BuiltinRuleEvidence::RealArithmeticMembershipClosure(_)
        | BuiltinRuleEvidence::NativeConstantMembership(_)
        | BuiltinRuleEvidence::NotEqualSymmetry
        | BuiltinRuleEvidence::SetRelationDuality(_)
        | BuiltinRuleEvidence::Set(_)
        | BuiltinRuleEvidence::FiniteSet(_)
        | BuiltinRuleEvidence::ListSetMembership(_)
        | BuiltinRuleEvidence::TupleLiteralShape
        | BuiltinRuleEvidence::PrimeU64Reflection
        | BuiltinRuleEvidence::CoprimeNaturalReflection
        | BuiltinRuleEvidence::StandardSetMembershipProjection
        | BuiltinRuleEvidence::StandardSetSubset => None,
    }
}

pub(super) fn validate_complex_algebraic_normalization_builtin_rule_evidence(
    target: &Fact,
    evidence: &ComplexAlgebraicNormalizationBuiltinRuleEvidence,
) -> Result<(), String> {
    if evidence.expected_target.to_string() != target.to_string() {
        return Err("complex-algebraic-normalization evidence changed its target".into());
    }
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = target else {
        return Err("complex-algebraic-normalization evidence targets a non-equality fact".into());
    };
    if !objs_equal_by_complex_rational_expression_evaluation(&equality.left, &equality.right) {
        return Err(
            "complex-algebraic-normalization evidence does not reproduce its exact equality".into(),
        );
    }
    let zero: Obj = Number::new("0".to_string()).into();
    let reproduced_nonzero_premises =
        complex_algebraic_normalization_nonzero_requirements(&equality.left, &equality.right)
            .into_iter()
            .map(|object| {
                Fact::from(AtomicFact::NotEqualFact(NotEqualFact::new(
                    object,
                    zero.clone(),
                    equality.line_file.clone(),
                )))
            })
            .collect::<Vec<_>>();
    if reproduced_nonzero_premises.len() != evidence.expected_nonzero_premises.len()
        || reproduced_nonzero_premises
            .iter()
            .zip(evidence.expected_nonzero_premises.iter())
            .any(|(reproduced, retained)| reproduced.to_string() != retained.to_string())
    {
        return Err(
            "complex-algebraic-normalization evidence changed its ordered nonzero premises".into(),
        );
    }
    Ok(())
}

pub(super) fn validate_scoped_fact_check_result(
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

pub(super) fn fact_is_supported_by_direct_named_theorem(fact: &Fact) -> bool {
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

pub(super) fn validate_direct_named_theorem_conclusion_well_definedness(
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
    validate_single_fact_store_output(
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
    validate_success_store_fact_result(
        &body.store,
        &body.proposition,
        "existential theorem conclusion body WD",
    )?;
    Ok(())
}

pub(super) fn validate_atomic_fact_well_definedness_result(
    result: &SuccessVerifyFactWellDefinedResult,
    source_fact: &Fact,
) -> Result<(), String> {
    let Some(recursive) = result.recursive.as_deref() else {
        return Err("atomic fact has no atomic well-definedness result".into());
    };
    validate_atomic_fact_well_definedness_proof_result(recursive, source_fact)
}

pub(super) fn validate_chain_fact_well_definedness_result(
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

pub(super) fn validate_atomic_fact_well_definedness_proof_result(
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

pub(super) fn fact_result_contains_inferred_facts(result: &SuccessFactStmtResult) -> bool {
    !result.store.infers.rule_applications.is_empty()
        || result
            .store
            .infers
            .store_fact_outputs
            .iter()
            .any(|output| !output.inferred_facts.is_empty() || !output.inferred_fact_ids.is_empty())
}

pub(super) fn direct_forall_result_publication_selections(
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
    let source_conclusion_keys = source_forall
        .then_facts
        .iter()
        .map(|fact| fact.clone().to_fact().to_string())
        .collect::<Vec<_>>();

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
        }]);
    }

    let mut saw_transient_source = false;
    let mut selections = Vec::new();
    let mut selected_source_conclusions = HashSet::new();
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
        let mut source_conclusion_indices = Vec::with_capacity(projected.then_facts.len());
        let mut used_inside_projection = HashSet::new();
        for projected_conclusion in &projected.then_facts {
            let projected_key = projected_conclusion.clone().to_fact().to_string();
            let Some(source_index) = source_conclusion_keys
                .iter()
                .enumerate()
                .find(|(index, source_key)| {
                    !used_inside_projection.contains(index) && **source_key == projected_key
                })
                .map(|(index, _)| index)
            else {
                return Err("stored ForallProof projection introduced a new conclusion".into());
            };
            if !selected_source_conclusions.insert(source_index) {
                return Err("stored ForallProof projections duplicated a conclusion".into());
            }
            used_inside_projection.insert(source_index);
            source_conclusion_indices.push(source_index);
        }
        selections.push(DirectForallResultPublicationSelection {
            forall_fact: projected.clone(),
            stored_fact_id: Some(stored_fact_id),
            source_parameter_indices,
            source_conclusion_indices,
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
        }]);
    }
    if selected_source_conclusions.len() != source_forall.then_facts.len() {
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

pub(super) fn direct_forall_parameter_types_match_for_projection(
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

pub(super) fn validate_success_obj_well_defined_result(
    result: &SuccessVerifyObjWellDefinedResult,
    expected_object: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = result as *const SuccessVerifyObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => {
            if obj_equality_key(&direct.object) != obj_equality_key(expected_object) {
                return Err("object WD result changed its checked object".into());
            }
            if let Some(binder) = &direct.steps.binder {
                validate_success_obj_binder_well_defined_result(binder, expected_object, visited)?;
            }
            for child in &direct.steps.children {
                validate_success_obj_well_defined_result(
                    child.result.as_ref(),
                    &child.source_object,
                    visited,
                )?;
            }
            for check in &direct.steps.fact_checks {
                if check.expected_proposition.to_string() != check.verification.fact().to_string() {
                    return Err("object WD fact check changed its verified proposition".into());
                }
            }
            for requirement in &direct.steps.target_requirements {
                if requirement.expected_proposition.to_string()
                    != requirement.verification.fact().to_string()
                {
                    return Err("object WD target requirement changed its proposition".into());
                }
            }
        }
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
            if obj_equality_key(&reuse.object) != obj_equality_key(expected_object) {
                return Err("reused object WD result changed its checked object".into());
            }
            validate_success_obj_well_defined_result(
                reuse.source.as_ref(),
                expected_object,
                visited,
            )?;
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(_) => {
            return Err("object WD result retained an unresolved recursive reference".into());
        }
    }
    Ok(())
}

pub(super) fn collect_well_definedness_to_lean_context_from_fact_result(
    result: &SuccessVerifyFactWellDefinedProofResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    match result {
        SuccessVerifyFactWellDefinedProofResult::AtomicFact(result) => {
            for argument in &result.arguments {
                let mut visited = HashSet::new();
                collect_well_definedness_to_lean_context_from_object_result(
                    &argument.source_object,
                    &argument.result,
                    context,
                    &mut visited,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::AndFact(result) => {
            for child in &result.conjuncts {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ChainFact(result) => {
            for child in &result.comparisons {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::OrFact(result) => {
            for child in &result.branches {
                collect_well_definedness_to_lean_context_from_fact_result(child, context)?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ExistFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_binder(&result.binder, context)?;
            for child in &result.body {
                collect_well_definedness_to_lean_context_from_fact_result(
                    &child.well_definedness,
                    context,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ForallFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_binder(&result.binder, context)?;
            for child in result.premises.iter().chain(result.conclusions.iter()) {
                collect_well_definedness_to_lean_context_from_fact_result(
                    &child.well_definedness,
                    context,
                )?;
            }
        }
        SuccessVerifyFactWellDefinedProofResult::ForallFactWithIff(result) => {
            collect_well_definedness_to_lean_context_from_fact_result(&result.forward, context)?;
            collect_well_definedness_to_lean_context_from_fact_result(&result.reverse, context)?;
        }
        SuccessVerifyFactWellDefinedProofResult::NotForallFact(result) => {
            collect_well_definedness_to_lean_context_from_fact_result(&result.inner, context)?;
        }
    }
    Ok(())
}

pub(super) fn success_verify_fact_result_is_deferred_plain_citation(
    verification: &SuccessVerifyFactResult,
) -> bool {
    match verification.proof() {
        SuccessFactProofResult::StoredFactCitation(_) => true,
        SuccessFactProofResult::Reuse(reuse) => {
            success_verify_fact_result_is_deferred_plain_citation(reuse.source.as_ref())
        }
        _ => false,
    }
}

pub(super) fn render_deferred_plain_fact_result_citation(
    verification: &SuccessVerifyFactResult,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match verification.proof() {
        SuccessFactProofResult::StoredFactCitation(citation)
            if success_verify_fact_result_is_deferred_plain_citation(verification) =>
        {
            let source = citation.source_fact.clone();
            if source.to_string() != verification.fact().to_string() {
                return Err("deferred WD citation changed its target proposition".into());
            }
            resolve_fact_citation(&citation.source_fact_id, &source, context)
        }
        SuccessFactProofResult::Reuse(reuse) => {
            render_deferred_plain_fact_result_citation(reuse.source.as_ref(), context)
        }
        _ => Err("WD requirement is not a deferred plain FactId citation".into()),
    }
}

pub(super) fn render_function_application_requirement_proof(
    requirement: &StmtResultFunctionApplicationRequirementToLeanCompilationContext,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    match &requirement.proof_expression {
        Some(proof_expression) => Ok(proof_expression.clone()),
        None => match render_deferred_plain_fact_result_citation(
            requirement.verification.as_ref(),
            context,
        ) {
            Ok(proof_expression) => Ok(proof_expression),
            Err(_) => {
                // This is a lexical recursive read of the canonical Result,
                // not a second lowering IR. No top-level declarations may be
                // created while constructing a local requirement proof.
                let mut nested_compiler = StmtResultToLeanCompiler::new("nested WD Result");
                nested_compiler.environment_stack = context.clone();
                let proof_expression = nested_compiler
                    .construct_lean_proof_from_shared_verify_fact_result(
                        requirement.verification.as_ref(),
                    )?
                    .ok_or_else(|| {
                        "nested WD requirement Result has no direct Lean proof constructor"
                            .to_string()
                    })?;
                if !nested_compiler.declarations.is_empty() {
                    return Err(
                        "nested WD requirement attempted to emit a top-level Lean declaration"
                            .into(),
                    );
                }
                Ok(proof_expression)
            }
        },
    }
}

pub(super) fn collect_well_definedness_to_lean_context_from_fact_binder(
    binder: &SuccessVerifyFactBinderResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    for group in &binder.parameter_groups {
        if let Some(carrier) = &group.carrier {
            let mut visited = HashSet::new();
            collect_well_definedness_to_lean_context_from_object_result(
                &carrier.source_object,
                &carrier.result,
                context,
                &mut visited,
            )?;
        }
        for premise in &group.parameters {
            collect_well_definedness_parameter_fact_alias(premise, context)?;
            if let Some(recursive) = premise.well_definedness.recursive.as_deref() {
                collect_well_definedness_to_lean_context_from_fact_result(recursive, context)?;
            }
        }
    }
    Ok(())
}

pub(super) fn collect_well_definedness_parameter_fact_alias(
    premise: &SuccessVerifyBinderPremiseResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Some(symbol_id) = premise.symbol_id else {
        return Ok(());
    };
    let fact_id = fact_id_for_well_definedness_binder_premise(premise)?;
    if !context.parameter_fact_aliases.iter().any(|alias| {
        alias.symbol_id == symbol_id
            && alias.fact_id == fact_id
            && alias.proposition.to_string() == premise.proposition.to_string()
    }) {
        context
            .parameter_fact_aliases
            .push(StmtResultWellDefinednessParameterFactAlias {
                symbol_id,
                fact_id,
                proposition: premise.proposition.clone(),
            });
    }
    Ok(())
}

pub(super) fn fact_id_for_well_definedness_binder_premise(
    premise: &SuccessVerifyBinderPremiseResult,
) -> Result<FactId, String> {
    premise
        .infers
        .store_fact_outputs
        .iter()
        .find(|output| {
            output.itself_and_why_itself_is_stored.0.to_string() == premise.proposition.to_string()
        })
        .and_then(|output| output.fact_id)
        .ok_or_else(|| {
            format!(
                "binder premise `{}` has no frozen ordinary FactId",
                premise.proposition
            )
        })
}

pub(super) fn direct_object_well_definedness_result(
    result: &SuccessVerifyObjWellDefinedResult,
) -> Result<&SuccessVerifyDirectObjWellDefinedResult, String> {
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(result) => Ok(result),
        SuccessVerifyObjWellDefinedResult::Reuse(result) => {
            direct_object_well_definedness_result(result.source.as_ref())
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(result) => Err(format!(
            "object WD recursive reference `{}` has no concrete compiler node",
            result.object
        )),
    }
}

pub(super) fn collect_well_definedness_to_lean_context_from_object_result(
    source_object: &Obj,
    result: &Rc<SuccessVerifyObjWellDefinedResult>,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = Rc::as_ptr(result) as usize;
    if !visited.insert(result_address) {
        if matches!(source_object, Obj::FnObj(_)) {
            collect_function_application_well_definedness_to_lean_context(
                source_object,
                direct_object_well_definedness_result(result.as_ref())?,
                context,
            )?;
        }
        return Ok(());
    }
    let direct = direct_object_well_definedness_result(result.as_ref())?;
    if obj_equality_key(source_object) != obj_equality_key(&direct.object) {
        return Err(format!(
            "object WD Result changed `{source_object}` to `{}`",
            direct.object
        ));
    }
    if matches!(source_object, Obj::FnObj(_)) {
        collect_function_application_well_definedness_to_lean_context(
            source_object,
            direct,
            context,
        )?;
    }
    for child in &direct.steps.children {
        collect_well_definedness_to_lean_context_from_object_result(
            &child.source_object,
            &child.result,
            context,
            visited,
        )?;
    }
    if let Some(binder) = &direct.steps.binder {
        collect_well_definedness_to_lean_context_from_object_binder(
            source_object,
            binder,
            context,
            visited,
        )?;
    }
    Ok(())
}

pub(super) fn collect_well_definedness_to_lean_context_from_object_child(
    child: &SuccessVerifyChildObjWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    collect_well_definedness_to_lean_context_from_object_result(
        &child.source_object,
        &child.result,
        context,
        visited,
    )
}

pub(super) fn collect_well_definedness_to_lean_context_from_object_binder(
    owner_object: &Obj,
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match binder {
        SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result) => {
            collect_well_definedness_to_lean_context_from_object_child(
                &result.parameter_carrier,
                context,
                visited,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                std::slice::from_ref(&result.parameter),
                context,
            )?;
            for condition in &result.conditions {
                if let Some(recursive) = condition.well_definedness.recursive.as_deref() {
                    collect_well_definedness_to_lean_context_from_fact_result(recursive, context)?;
                }
            }
        }
        SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result) => {
            for child in &result.parameter_carriers {
                collect_well_definedness_to_lean_context_from_object_child(
                    child, context, visited,
                )?;
            }
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.parameters,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.domains,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.return_carrier,
                context,
                visited,
            )?;
        }
        SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result) => {
            for child in &result.parameter_carriers {
                collect_well_definedness_to_lean_context_from_object_child(
                    child, context, visited,
                )?;
            }
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.parameters,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_binder_premises(
                &result.domains,
                context,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.return_carrier,
                context,
                visited,
            )?;
            collect_well_definedness_to_lean_context_from_object_child(
                &result.body,
                context,
                visited,
            )?;
            collect_anonymous_function_well_definedness_to_lean_context(
                owner_object,
                result,
                context,
            )?;
        }
        // These constructor-specific binders already publish every object
        // dependency through `steps.children`; they do not introduce
        // parameter aliases consumed by the current Lean surface.
        SuccessVerifyBinderObjectWellDefinedResult::Iteration(_)
        | SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(_)
        | SuccessVerifyBinderObjectWellDefinedResult::Reduce(_)
        | SuccessVerifyBinderObjectWellDefinedResult::Structure(_) => {}
    }
    Ok(())
}

pub(super) fn collect_well_definedness_to_lean_context_from_binder_premises(
    premises: &[SuccessVerifyBinderPremiseResult],
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    for premise in premises {
        collect_well_definedness_parameter_fact_alias(premise, context)?;
        if let Some(recursive) = premise.well_definedness.recursive.as_deref() {
            collect_well_definedness_to_lean_context_from_fact_result(recursive, context)?;
        }
    }
    Ok(())
}

pub(super) fn well_definedness_binder_premise_to_lean_compilation_context(
    premise: &SuccessVerifyBinderPremiseResult,
) -> Result<StmtResultWellDefinednessBinderPremiseToLeanCompilationContext, String> {
    Ok(
        StmtResultWellDefinednessBinderPremiseToLeanCompilationContext {
            role: premise.role,
            symbol_id: premise.symbol_id,
            fact_id: fact_id_for_well_definedness_binder_premise(premise)?,
            proposition: premise.proposition.clone(),
        },
    )
}

pub(super) fn collect_anonymous_function_well_definedness_to_lean_context(
    owner_object: &Obj,
    result: &SuccessVerifyAnonymousFunctionWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Obj::AnonymousFn(source_function) = owner_object else {
        return Err("anonymous-function WD binder changed its owner object".into());
    };
    let occurrence_id = source_function.source_occurrence_id.ok_or_else(|| {
        "anonymous function WD Result has no parser-owned occurrence id".to_string()
    })?;
    let parameters = result
        .parameters
        .iter()
        .map(well_definedness_binder_premise_to_lean_compilation_context)
        .collect::<Result<Vec<_>, _>>()?;
    let domains = result
        .domains
        .iter()
        .map(well_definedness_binder_premise_to_lean_compilation_context)
        .collect::<Result<Vec<_>, _>>()?;
    let mut assumption_infers = SuccessInferResult::new();
    for premise in result.parameters.iter().chain(result.domains.iter()) {
        assumption_infers.new_infer_result_inside(premise.infers.clone());
    }
    context.anonymous_functions.insert(
        occurrence_id,
        StmtResultAnonymousFunctionWellDefinednessToLeanCompilationContext {
            source_function: owner_object.clone(),
            parameters,
            domains,
            assumption_infers,
            compiled_inference_fact_proof_steps: Vec::new(),
            closure: StmtResultAnonymousFunctionClosureToLeanCompilationContext {
                role: result.body_membership.role,
                expected_proposition: result.body_membership.expected_proposition.clone(),
                verification: result.body_membership.verification.clone(),
                proof_expression: None,
            },
        },
    );
    Ok(())
}

pub(super) fn collect_function_application_well_definedness_to_lean_context(
    source_object: &Obj,
    root: &SuccessVerifyDirectObjWellDefinedResult,
    context: &mut StmtResultWellDefinednessToLeanCompilationContext,
) -> Result<(), String> {
    let Obj::FnObj(source_application) = source_object else {
        return Ok(());
    };
    let Some(occurrence_id) = source_application.source_occurrence_id else {
        // Multi-layer WD Results contain synthetic prefix nodes such as
        // `g(a)` underneath the one parser-owned `g(a)(b)` occurrence. The
        // outer Result collects every layer from its FunctionPrefix edges;
        // the synthetic child therefore has no independent context key.
        return Ok(());
    };
    let layer_count = source_application.body.len();
    if layer_count == 0 {
        return Err("function application retained no argument layers".into());
    }
    let mut layer_results = vec![None; layer_count];
    let mut current = root;
    for layer_index in (0..layer_count).rev() {
        let source_prefix: Obj = source_application.prefix_obj(layer_index + 1);
        if obj_equality_key(&current.object) != obj_equality_key(&source_prefix) {
            return Err(format!(
                "function application layer {layer_index} changed its Result-owned source prefix"
            ));
        }
        layer_results[layer_index] = Some(current);
        if layer_index == 0 {
            continue;
        }
        let prefix_children = current
            .steps
            .children
            .iter()
            .filter(|child| {
                child.role
                    == (WellDefinedObjChildRole::FunctionPrefix {
                        through_layer_index: layer_index - 1,
                    })
            })
            .collect::<Vec<_>>();
        let [prefix_child] = prefix_children.as_slice() else {
            return Err(format!(
                "function application layer {layer_index} requires one exact FunctionPrefix child Result"
            ));
        };
        current = direct_object_well_definedness_result(prefix_child.result.as_ref())?;
    }
    let first_layer = layer_results[0].expect("every application layer was retained");
    let anonymous_function_head = first_layer
        .steps
        .children
        .iter()
        .find(|child| child.role == WellDefinedObjChildRole::FunctionHead)
        .map(|child| child.source_object.clone());
    let layers = layer_results
        .into_iter()
        .map(|layer| {
            let layer = layer.expect("every application layer was retained");
            StmtResultFunctionApplicationLayerWellDefinednessToLeanCompilationContext {
                source_prefix: layer.object.clone(),
                function_contracts: layer.cache_key.function_contracts.clone(),
                intrinsic_result_set: layer.intrinsic_result_set.clone(),
                requirements: layer
                    .steps
                    .target_requirements
                    .iter()
                    .map(|requirement| {
                        StmtResultFunctionApplicationRequirementToLeanCompilationContext {
                            role: requirement.role,
                            expected_proposition: requirement.expected_proposition.clone(),
                            verification: requirement.verification.clone(),
                            proof_expression: None,
                        }
                    })
                    .collect(),
            }
        })
        .collect();
    let application_context =
        StmtResultFunctionApplicationWellDefinednessToLeanCompilationContext {
            source_application: source_object.clone(),
            function_contracts: root.cache_key.function_contracts.clone(),
            anonymous_function_head,
            layers,
        };
    if let Some(previous) = context
        .function_applications
        .insert(occurrence_id, application_context)
    {
        if obj_equality_key(&previous.source_application) != obj_equality_key(source_object) {
            return Err(format!(
                "function application occurrence {} was reused for another source object",
                occurrence_id.value()
            ));
        }
    }
    Ok(())
}

/// Consume the intrinsic stores inside one recursive fact-WD child while the
/// compiler already has the complete parent-owned WD tree active. This keeps
/// nested binder context available without manufacturing a duplicate child
/// statement certificate.
pub(super) fn install_fact_well_definedness_proof_store_results_in_active_environment(
    result: &SuccessVerifyFactWellDefinedProofResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(), String> {
    let SuccessVerifyFactWellDefinedProofResult::AtomicFact(atomic) = result else {
        return Ok(());
    };
    let mut visited = HashSet::new();
    for argument in &atomic.arguments {
        install_object_well_definedness_store_results(
            argument.result.as_ref(),
            environment_stack,
            &mut visited,
        )?;
    }
    Ok(())
}

pub(super) fn install_object_well_definedness_store_results(
    result: &SuccessVerifyObjWellDefinedResult,
    environment_stack: &mut StmtResultToLeanCompilerEnvironmentStack,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    let result_address = result as *const SuccessVerifyObjWellDefinedResult as usize;
    if !visited.insert(result_address) {
        return Ok(());
    }
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => {
            for child in &direct.steps.children {
                install_object_well_definedness_store_results(
                    child.result.as_ref(),
                    environment_stack,
                    visited,
                )?;
            }
            for store in &direct.steps.stores {
                let result_set = direct.intrinsic_result_set.as_ref().ok_or_else(|| {
                    format!(
                        "object WD stored `{}` without an intrinsic result set",
                        store.fact
                    )
                })?;
                let expected: Fact = InFact::new(
                    direct.object.clone(),
                    result_set.clone(),
                    store.fact.line_file(),
                )
                .into();
                if store.fact.to_string() != expected.to_string() {
                    return Err(format!(
                        "object WD store changed intrinsic membership `{expected}` to `{}`",
                        store.fact
                    ));
                }
                let fact_id = store.fact_id.ok_or_else(|| {
                    format!("object WD intrinsic-result store `{expected}` has no FactId")
                })?;
                let matching_source_outputs = store
                    .infers
                    .store_fact_outputs
                    .iter()
                    .filter(|output| {
                        output.fact_id == Some(fact_id)
                            && output.itself_and_why_itself_is_stored.0.to_string()
                                == expected.to_string()
                    })
                    .count();
                if matching_source_outputs != 1 {
                    return Err(format!(
                        "object WD intrinsic-result store `{expected}` lost its exact source store output"
                    ));
                }
                // Multi-layer application checking synthesizes prefix nodes
                // such as `g(a)` underneath the parser-owned occurrence
                // `g(a)(b)`. Their store Results and FactIds remain validated
                // above, but they are local construction evidence rather than
                // independently citable source expressions. The enclosing
                // application renderer consumes the exact FunctionPrefix edge
                // and constructs this membership with `Litex.In.own`; do not
                // invent a parser occurrence merely to publish a duplicate
                // compiler binding for the synthetic prefix.
                if matches!(&direct.object, Obj::FnObj(application) if application.source_occurrence_id.is_none())
                {
                    continue;
                }
                let rendered_object = render_obj(&direct.object, environment_stack)?;
                let rendered_set = render_obj(result_set, environment_stack)?;
                let proof = format!("Litex.In.own {rendered_set} {rendered_object}");
                if let Some(existing) = environment_stack.fact_propositions.get(&fact_id) {
                    if existing.to_string() != expected.to_string()
                        && !membership_facts_are_equal_up_to_nested_binder_alpha(
                            existing, &expected,
                        )
                    {
                        return Err(format!(
                            "object WD FactId `{fact_id}` changed from `{existing}` to `{expected}`"
                        ));
                    }
                }
                environment_stack.fact_names.insert(fact_id, proof);
                environment_stack
                    .fact_propositions
                    .insert(fact_id, expected);
            }
            if let Some(instantiation) = direct.steps.template_instantiation.as_deref() {
                install_template_instantiation_result(
                    &direct.object,
                    instantiation,
                    environment_stack,
                )?;
            }
            Ok(())
        }
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
            install_object_well_definedness_store_results(
                reuse.source.as_ref(),
                environment_stack,
                visited,
            )
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(_) => Ok(()),
    }
}

pub(super) fn object_well_definedness_result_contains_intrinsic_store(
    result: &SuccessVerifyObjWellDefinedResult,
) -> bool {
    match result {
        SuccessVerifyObjWellDefinedResult::Direct(direct) => {
            direct.steps.template_instantiation.is_some()
                || !direct.steps.stores.is_empty()
                || direct.steps.children.iter().any(|child| {
                    object_well_definedness_result_contains_intrinsic_store(child.result.as_ref())
                })
        }
        SuccessVerifyObjWellDefinedResult::Reuse(reuse) => {
            object_well_definedness_result_contains_intrinsic_store(reuse.source.as_ref())
        }
        SuccessVerifyObjWellDefinedResult::RecursiveReference(_) => false,
    }
}

pub(super) fn install_template_instantiation_result(
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
        || expected_application.symbol.id() != application.symbol.id()
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
    if let Some(previous) = environment_stack
        .symbol_names
        .insert(application.symbol.id(), rendered_application.clone())
    {
        if previous != rendered_application {
            return Err(format!(
                "Template application `{application}` changed its compiled binding"
            ));
        }
    }

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

pub(super) fn validate_success_obj_binder_well_defined_result(
    binder: &SuccessVerifyBinderObjectWellDefinedResult,
    owner: &Obj,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    match (binder, owner) {
        (SuccessVerifyBinderObjectWellDefinedResult::SetBuilder(result), Obj::SetBuilder(_)) => {
            validate_success_obj_well_defined_child(&result.parameter_carrier, visited)?;
        }
        (SuccessVerifyBinderObjectWellDefinedResult::FunctionSet(result), Obj::FnSet(_)) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::AnonymousFunction(result),
            Obj::AnonymousFn(_),
        ) => {
            validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
            validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
            validate_success_obj_well_defined_child(&result.body, visited)?;
            validate_success_obj_target_requirement(&result.body_membership)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Iteration(result),
            Obj::Sum(_) | Obj::Product(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            validate_success_iteration_interval_result(&result.interval, visited)?;
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::FiniteAggregate(result),
            Obj::SumOfFiniteSet(_) | Obj::ProductOfFiniteSet(_),
        ) => {
            if let Some(scalar_return) = &result.scalar_return {
                validate_success_iteration_scalar_return_result(scalar_return, visited)?;
            }
            match &result.mode {
                SuccessVerifyFiniteAggregateModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_set)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::ClosedRange(result) => {
                    validate_success_obj_well_defined_child(&result.aggregate_dependency, visited)?;
                }
                SuccessVerifyFiniteAggregateModeResult::Symbolic(_) => {}
            }
        }
        (
            SuccessVerifyBinderObjectWellDefinedResult::Reduce(result),
            Obj::Reduce(_) | Obj::FiniteSetReduce(_),
        ) => {
            validate_success_obj_fact_check(&result.seed_membership)?;
            if let Some(laws) = &result.operation_laws {
                validate_success_obj_well_defined_child(&laws.parameter_carrier, visited)?;
                validate_success_obj_fact_check(&laws.associativity)?;
                validate_success_obj_fact_check(&laws.commutativity)?;
            }
            match &result.mode {
                SuccessVerifyReduceModeResult::Empty(result) => {
                    validate_success_obj_fact_check(&result.empty_range_or_set)?;
                }
                SuccessVerifyReduceModeResult::Interval(result) => {
                    validate_success_iteration_interval_result(&result.interval, visited)?;
                }
                SuccessVerifyReduceModeResult::Elements(result) => {
                    for membership in &result.body_memberships {
                        validate_success_obj_fact_check(membership)?;
                    }
                    validate_success_obj_well_defined_children(&result.applications, visited)?;
                }
                SuccessVerifyReduceModeResult::Symbolic(result) => {
                    if let SuccessVerifyFiniteReduceDomainCoverageResult::Subset(result) =
                        &result.coverage
                    {
                        validate_success_obj_fact_check(&result.subset)?;
                    }
                }
            }
        }
        (SuccessVerifyBinderObjectWellDefinedResult::Structure(result), Obj::StructObj(_)) => {
            for argument in &result.header_arguments {
                validate_success_obj_fact_check(&argument.verification)?;
            }
            for domain in &result.header_domains {
                validate_success_obj_fact_check(domain)?;
            }
            for field in &result.fields {
                validate_success_obj_well_defined_child(&field.carrier, visited)?;
            }
        }
        _ => {
            return Err(format!(
                "object `{owner}` retained a well-definedness binder owned by another constructor"
            ));
        }
    }
    Ok(())
}

pub(super) fn validate_success_iteration_scalar_return_result(
    result: &SuccessVerifyIterationScalarReturnResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    validate_success_obj_fact_check(&result.return_subset)
}

pub(super) fn validate_success_iteration_interval_result(
    result: &SuccessVerifyIterationIntervalResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_children(&result.parameter_carriers, visited)?;
    validate_success_obj_well_defined_child(&result.return_carrier, visited)?;
    if let Some(body) = &result.body {
        validate_success_obj_well_defined_child(body, visited)?;
    }
    if let Some(body_membership) = &result.body_membership {
        validate_success_obj_target_requirement(body_membership)?;
    }
    match &result.coverage {
        SuccessVerifyIterationCoverageResult::UniversalIntegerCarrier(_) => {}
        SuccessVerifyIterationCoverageResult::Enumerated(result) => {
            for check in &result.checks {
                validate_success_obj_fact_check(check)?;
            }
        }
        SuccessVerifyIterationCoverageResult::Endpoint(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
        SuccessVerifyIterationCoverageResult::IntervalSubset(result) => {
            validate_success_obj_fact_check(&result.check)?;
        }
    }
    Ok(())
}

pub(super) fn validate_success_obj_well_defined_children(
    children: &[SuccessVerifyChildObjWellDefinedResult],
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    for child in children {
        validate_success_obj_well_defined_child(child, visited)?;
    }
    Ok(())
}

pub(super) fn validate_success_obj_well_defined_child(
    child: &SuccessVerifyChildObjWellDefinedResult,
    visited: &mut HashSet<usize>,
) -> Result<(), String> {
    validate_success_obj_well_defined_result(child.result.as_ref(), &child.source_object, visited)
}

pub(super) fn validate_success_obj_fact_check(
    check: &SuccessVerifyFactForObjWellDefinedResult,
) -> Result<(), String> {
    if check.expected_proposition.to_string() != check.verification.fact().to_string() {
        return Err("binder WD fact check changed its verified proposition".into());
    }
    Ok(())
}

pub(super) fn validate_success_obj_target_requirement(
    requirement: &SuccessVerifyObjTargetRequirementResult,
) -> Result<(), String> {
    if requirement.expected_proposition.to_string() != requirement.verification.fact().to_string() {
        return Err("binder WD target requirement changed its verified proposition".into());
    }
    Ok(())
}

pub(super) fn validate_success_evaluate_obj_result(
    result: &SuccessEvaluateObjResult,
) -> Result<(), String> {
    let recomputed = result
        .expression
        .evaluate_to_normalized_decimal_number_with_result()
        .ok_or_else(|| "closed numeric evaluation expression no longer evaluates".to_string())?;
    compare_success_evaluate_obj_results(result, &recomputed)
}

pub(super) fn compare_success_evaluate_obj_results(
    retained: &SuccessEvaluateObjResult,
    recomputed: &SuccessEvaluateObjResult,
) -> Result<(), String> {
    if obj_equality_key(&retained.expression) != obj_equality_key(&recomputed.expression)
        || retained.value.normalized_value != recomputed.value.normalized_value
    {
        return Err("closed numeric evaluation changed its expression or value".into());
    }
    match (&retained.step, &recomputed.step) {
        (
            SuccessEvaluateObjStepResult::Literal(retained),
            SuccessEvaluateObjStepResult::Literal(recomputed),
        ) if retained.literal.normalized_value == recomputed.literal.normalized_value => Ok(()),
        (
            SuccessEvaluateObjStepResult::Unary(retained),
            SuccessEvaluateObjStepResult::Unary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.argument, &recomputed.argument)
        }
        (
            SuccessEvaluateObjStepResult::Binary(retained),
            SuccessEvaluateObjStepResult::Binary(recomputed),
        ) if retained.operator == recomputed.operator => {
            compare_success_evaluate_obj_results(&retained.left, &recomputed.left)?;
            compare_success_evaluate_obj_results(&retained.right, &recomputed.right)
        }
        (
            SuccessEvaluateObjStepResult::Shape(retained),
            SuccessEvaluateObjStepResult::Shape(recomputed),
        ) if retained.operator == recomputed.operator
            && retained.inputs.len() == recomputed.inputs.len()
            && retained.evaluated_children.len() == recomputed.evaluated_children.len() =>
        {
            for (retained_input, recomputed_input) in
                retained.inputs.iter().zip(recomputed.inputs.iter())
            {
                if obj_equality_key(retained_input) != obj_equality_key(recomputed_input) {
                    return Err("closed numeric shape evaluation changed an input".into());
                }
            }
            for (retained_child, recomputed_child) in retained
                .evaluated_children
                .iter()
                .zip(recomputed.evaluated_children.iter())
            {
                compare_success_evaluate_obj_results(retained_child, recomputed_child)?;
            }
            Ok(())
        }
        _ => Err("closed numeric evaluation changed its recursive operation tree".into()),
    }
}
