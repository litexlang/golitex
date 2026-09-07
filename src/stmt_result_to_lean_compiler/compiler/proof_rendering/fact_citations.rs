//! Exact fact and universal-conclusion citations.

use super::super::*;

pub(in super::super) fn resolve_fact_citation(
    source_fact_id: &FactId,
    expected: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let retained = context
        .fact_propositions
        .get(source_fact_id)
        .ok_or_else(|| {
            let mut visible_fact_ids = context
                .fact_propositions
                .keys()
                .copied()
                .collect::<Vec<_>>();
            visible_fact_ids.sort();
            let visible_fact_ids = visible_fact_ids
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "unavailable cited fact `{source_fact_id}` for expected proposition `{expected}`; visible exact FactIds: [{visible_fact_ids}]"
            )
        })?;
    let same_proposition = if retained.to_string() == expected.to_string() {
        true
    } else if membership_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if equality_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if subset_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if nonempty_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if normal_atomic_facts_are_equal_up_to_nested_binder_alpha(retained, expected) {
        true
    } else if let (Fact::ForallFact(retained), Fact::ForallFact(expected)) = (retained, expected) {
        let runtime = Runtime::default();
        let retained_key = runtime
            .alpha_normalized_forall_cache_key(retained)
            .map_err(|error| {
                format!(
                    "cited FactId `{source_fact_id}` retained forall alpha key failed: {}",
                    error.trace_message()
                )
            })?;
        let expected_key = runtime
            .alpha_normalized_forall_cache_key(expected)
            .map_err(|error| {
                format!(
                    "cited FactId `{source_fact_id}` expected forall alpha key failed: {}",
                    error.trace_message()
                )
            })?;
        if retained_key == expected_key {
            true
        } else {
            let retained_rendered = render_forall_fact_type(retained, context).map_err(|error| {
                format!(
                    "{error}; retained alpha key `{retained_key}`; expected alpha key `{expected_key}`"
                )
            })?;
            retained_rendered == render_forall_fact_type(expected, context)?
        }
    } else if matches!(
        (retained, expected),
        (Fact::ExistFact(_), Fact::ExistFact(_))
    ) {
        one_witness_existentials_are_alpha_equal(retained, expected, context)?
    } else {
        false
    };
    if !same_proposition {
        return Err(format!(
            "cited FactId `{source_fact_id}` changed proposition from `{retained}` to `{expected}`"
        ));
    }
    if let Some(name) = context.fact_names.get(source_fact_id) {
        return Ok(name.clone());
    }
    let binding = context
        .forall_conclusion_bindings
        .get(source_fact_id)
        .ok_or_else(|| format!("cited FactId `{source_fact_id}` has no emitted Lean proof"))?;
    render_forall_conclusion_citation(binding, context)
}

pub(in super::super) fn normal_atomic_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(left)),
            Fact::AtomicFact(AtomicFact::NormalAtomicFact(right)),
        ) => {
            left.predicate.to_string() == right.predicate.to_string()
                && left.body.len() == right.body.len()
                && left
                    .body
                    .iter()
                    .zip(right.body.iter())
                    .all(|(left, right)| {
                        objs_equal_with_nested_binder_alpha_equivalence(left, right)
                    })
        }
        _ => false,
    }
}

pub(in super::super) fn nonempty_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(left)),
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(right)),
        ) => objs_equal_with_nested_binder_alpha_equivalence(&left.set, &right.set),
        _ => false,
    }
}

pub(in super::super) fn subset_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::SubsetFact(left)),
            Fact::AtomicFact(AtomicFact::SubsetFact(right)),
        ) => {
            objs_equal_with_nested_binder_alpha_equivalence(&left.left, &right.left)
                && objs_equal_with_nested_binder_alpha_equivalence(&left.right, &right.right)
        }
        _ => false,
    }
}

pub(in super::super) fn equality_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::EqualFact(left)),
            Fact::AtomicFact(AtomicFact::EqualFact(right)),
        ) => {
            objs_equal_with_nested_binder_alpha_equivalence(&left.left, &right.left)
                && objs_equal_with_nested_binder_alpha_equivalence(&left.right, &right.right)
        }
        _ => false,
    }
}

pub(in super::super) fn membership_facts_are_equal_up_to_nested_binder_alpha(
    left: &Fact,
    right: &Fact,
) -> bool {
    match (left, right) {
        (
            Fact::AtomicFact(AtomicFact::InFact(left)),
            Fact::AtomicFact(AtomicFact::InFact(right)),
        ) => {
            objs_equal_with_nested_binder_alpha_equivalence(&left.element, &right.element)
                && objs_equal_with_nested_binder_alpha_equivalence(&left.set, &right.set)
        }
        _ => false,
    }
}

pub(in super::super) fn render_forall_conclusion_citation(
    binding: &ForallConclusionBinding,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let parameters = binding
        .forall
        .typed_parameters
        .collect_param_bindings_with_types();
    if parameters.len() != binding.parameter_premises.len()
        || binding.forall.dom_facts.len() != binding.premises.len()
    {
        return Err("stored forall conclusion binding changed its premise arity".into());
    }
    let mut terms = vec![binding.theorem_name.clone()];
    for ((parameter, param_type), premise) in
        parameters.iter().zip(binding.parameter_premises.iter())
    {
        let argument = context
            .symbol_names
            .get(&parameter.id())
            .cloned()
            .ok_or_else(|| {
                format!(
                    "stored forall conclusion cannot resolve parameter `{}`",
                    parameter.name()
                )
            })?;
        terms.push(argument);
        if !matches!(
            param_type,
            ParamType::Set(_) | ParamType::Obj(Obj::StandardSet(StandardSet::Z))
        ) {
            terms.push(format!(
                "({})",
                resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
            ));
        }
    }
    for premise in &binding.premises {
        terms.push(format!(
            "({})",
            resolve_fact_citation(&premise.fact_id, &premise.fact, context)?
        ));
    }
    let application = format!("({})", terms.join(" "));
    conjunction_projection(
        &application,
        binding.conclusion_index,
        binding.conclusion_count,
    )
}
