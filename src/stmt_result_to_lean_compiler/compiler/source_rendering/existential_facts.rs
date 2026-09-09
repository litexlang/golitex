//! Existential fact rendering and witness-group equivalence.

use super::super::*;

pub(in super::super) fn render_existential_fact(
    existential: &ExistFact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let name = lean_identifier(group.params[0].name());
    render_existential_fact_with_names(existential, context, &name, &format!("__carrier_{name}"))
}

/// Render only the existence component of a checked `exist!` Result.  This is
/// used by function choice: the accompanying uniqueness Result is compiled as
/// a separate Lean proof, while `Classical.choose` consumes the ordinary
/// existence projection.  No source fact is weakened—the caller must compile
/// and validate the retained uniqueness child as well.
pub(in super::super) fn render_unique_existential_as_plain_existence(
    existential: &ExistFact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !existential.is_exist_unique() {
        return Err("unique-existence projection received a non-`exist!` fact".into());
    }
    render_existential_fact(
        &ExistFact::PlainExistFact(existential.spec().clone()),
        context,
    )
}

pub(in super::super) fn render_existential_fact_with_names(
    existential: &ExistFact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
    witness_name: &str,
    carrier_name: &str,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let set = parameter_set(&group.param_type)?;
    let mut nested = context.clone();
    nested
        .symbol_names
        .insert(group.params[0].id(), witness_name.to_string());
    nested
        .existential_names
        .insert(group.params[0].name().to_string(), witness_name.to_string());
    let requirement = format!("Litex.In {witness_name} {}", render_obj(set, &nested)?);
    // The body may pass the witness to an exact-carrier concrete predicate.
    // Bind the checked membership as data before rendering that body so every
    // use observes the same Result-owned representative.  The constructor and
    // `rcases` syntax remains `⟨witness, membership, body⟩`, while Lean's
    // type now records the dependency that a plain conjunction cannot express.
    let proof_name = format!("__type_{witness_name}");
    let lowered_set = LeanTargetObjectRepresentation::lower(set)?;
    let exact_numeric_carrier = existential_uses_exact_numeric_carrier(set)?;
    let exact_witness = if exact_numeric_carrier
        || matches!(
            lowered_set,
            LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex)
        ) {
        witness_name.to_string()
    } else {
        format!("(Litex.In.rep {witness_name} {proof_name})")
    };
    if exact_numeric_carrier {
        install_exact_predicate_carrier_value(
            group.params[0].id(),
            set,
            &exact_witness,
            &mut nested,
        )?;
    } else {
        nested
            .exact_carrier_values
            .insert(group.params[0].id(), exact_witness);
        install_numeric_representations_from_membership(
            group.params[0].id(),
            &lowered_set,
            witness_name,
            &proof_name,
            &mut nested,
        );
    }
    let aliases = nested
        .well_definedness
        .as_ref()
        .map(|well_definedness| {
            well_definedness
                .parameter_fact_aliases
                .iter()
                .filter(|alias| alias.symbol_id == group.params[0].id())
                .cloned()
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    if let Some(primary) = aliases.first() {
        install_parameter_fact_aliases(
            group.params[0].id(),
            primary.fact_id,
            &primary.proposition,
            &proof_name,
            set,
            &mut nested,
        )?;
        // `install_parameter_fact_aliases` intentionally selects `In.rep`
        // for an ordinary heterogeneous parameter.  This binder is already
        // the exact standard-set carrier, so restore the native identity after
        // installing only the Result-owned fact aliases.
        if exact_numeric_carrier {
            install_exact_predicate_carrier_value(
                group.params[0].id(),
                set,
                witness_name,
                &mut nested,
            )?;
        }
    }
    let body = render_fact(&existential.facts()[0].from_ref_to_cloned_fact(), &nested)?;
    let binders = match set {
        Obj::FnSet(_) => format!("({carrier_name} : Type 1) ({witness_name} : {carrier_name})"),
        set if set_requires_heterogeneous_carrier(set) => {
            format!("({carrier_name} : Type) ({witness_name} : {carrier_name})")
        }
        _ if exact_numeric_carrier => {
            format!("({witness_name} : ({}).Carrier)", render_obj(set, &nested)?)
        }
        _ => format!("({witness_name} : ℂ)"),
    };
    Ok(format!(
        "∃ {binders}, ∃ ({proof_name} : {requirement}), {body}"
    ))
}

/// Numeric existential witnesses bind the exact native carrier selected by
/// their declared standard set.  This preserves the identity of Mathlib-owned
/// witnesses (for example `q : ℚ` from rational density) instead of casting
/// them to `ℂ` and later trying to recover them through `In.rep`.
///
/// Set builders, ranges, arbitrary sets, and function sets keep their existing
/// reviewed representations.  Their dependent/subtype witness ABI is a
/// separate compiler family.
pub(in super::super) fn existential_uses_exact_numeric_carrier(set: &Obj) -> Result<bool, String> {
    let lowered = LeanTargetObjectRepresentation::lower(set)?;
    Ok(
        matches!(lowered, LeanTargetObjectRepresentation::StandardSet(_))
            && exact_set_numeric_value(&lowered, "__existential_witness").is_some(),
    )
}

pub(in super::super) fn one_witness_existential_group(
    existential: &ExistFact,
) -> Result<&TypedParameterGroup, String> {
    if !existential.is_plain_exist()
        || existential.typed_parameters().number_of_params() != 1
        || existential.facts().len() != 1
    {
        return Err(
            "compiler existential facts support one positive witness and one body fact".into(),
        );
    }
    let group = &existential.typed_parameters().groups[0];
    if group.params.len() != 1 {
        return Err("compiler existential fact requires one singleton parameter group".into());
    }
    parameter_set(&group.param_type)?;
    Ok(group)
}

pub(in super::super) fn one_witness_existentials_are_alpha_equal(
    source: &Fact,
    target: &Fact,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<bool, String> {
    let (Fact::ExistFact(source), Fact::ExistFact(target)) = (source, target) else {
        return Ok(false);
    };
    let source_group = one_witness_existential_group(source)?;
    let target_group = one_witness_existential_group(target)?;
    if source_group.param_type.to_string() != target_group.param_type.to_string() {
        return Ok(false);
    }
    let source_body = source.facts()[0].from_ref_to_cloned_fact();
    let target_body = target.facts()[0].from_ref_to_cloned_fact();
    Ok(fact_matches_structured_induction_goal_substitution(
        &source_body,
        &target_body,
        source_group.params[0].id(),
        &obj_for_bound_param_in_scope(&target_group.params[0]),
    ))
}
