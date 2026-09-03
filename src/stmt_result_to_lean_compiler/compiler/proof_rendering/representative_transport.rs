//! Equality and order transport across representatives.

use super::super::*;

pub(in super::super) fn render_equality_across_representative(
    equality: &EqualFact,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let source_left = render_obj(&equality.left, source)?;
    let source_right = render_obj(&equality.right, source)?;
    let target_left = render_obj(&equality.left, target)?;
    let target_right = render_obj(&equality.right, target)?;
    let left_changed = source_left == source_value && target_left == target_value;
    let right_changed = source_right == source_value && target_right == target_value;
    match (left_changed, right_changed) {
        (true, true) => Ok(format!("Litex.Same.refl ({target_value})")),
        (true, false) if source_right == target_right => Ok(format!(
            "Litex.Same.trans (Litex.Same.symm ({source_same_target})) ({source_proof})"
        )),
        (false, true) if source_left == target_left => Ok(format!(
            "Litex.Same.trans ({source_proof}) ({source_same_target})"
        )),
        (false, false) if source_left == target_left && source_right == target_right => {
            Ok(source_proof.into())
        }
        _ => Err(
            "compiler equality transport requires the changing value as a whole equality side"
                .into(),
        ),
    }
}

/// Observation-free counterpart of [`render_equality_across_representative`].
/// Set-builder membership exposes only the semantic `Same` edge (there is no
/// source-carrier observer to recover), so equality projection must remain in
/// that ABI all the way through the representative transport.
pub(in super::super) fn render_no_observation_equality_across_representative(
    equality: &EqualFact,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let source_left = render_obj(&equality.left, source)?;
    let source_right = render_obj(&equality.right, source)?;
    let target_left = render_obj(&equality.left, target)?;
    let target_right = render_obj(&equality.right, target)?;
    let left_changed = source_left == source_value && target_left == target_value;
    let right_changed = source_right == source_value && target_right == target_value;
    match (left_changed, right_changed) {
        (true, true) => Ok(format!(
            "Litex.Same.reflNoObservation ({target_value})"
        )),
        (true, false) if source_right == target_right => Ok(format!(
            "Litex.Same.transNoObservation (Litex.Same.symmNoObservation ({source_same_target})) ({source_proof})"
        )),
        (false, true) if source_left == target_left => Ok(format!(
            "Litex.Same.transNoObservation ({source_proof}) ({source_same_target})"
        )),
        (false, false) if source_left == target_left && source_right == target_right => {
            Ok(source_proof.into())
        }
        _ => Err(
            "compiler equality transport requires the changing value as a whole equality side"
                .into(),
        ),
    }
}

/// Transport the body of the compiler's supported one-witness existential
/// while retaining the same witness and membership certificate. Equality
/// bodies use the direct representative bridge; concrete predicate bodies use
/// their own definition-owned exact-parameter transport.
pub(in super::super) fn render_one_witness_existential_across_representative(
    existential: &ExistFactEnum,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let group = one_witness_existential_group(existential)?;
    let body = existential.facts()[0].from_ref_to_cloned_fact();
    let witness = "__transport_witness";
    let membership = "__transport_membership";
    let mut source_body = source.clone();
    let mut target_body = target.clone();
    for context in [&mut source_body, &mut target_body] {
        context
            .symbol_names
            .insert(group.params[0].id(), witness.to_string());
        context
            .existential_names
            .insert(group.params[0].name().to_string(), witness.to_string());
    }
    let transported_body = match &body {
        Fact::AtomicFact(AtomicFact::EqualFact(equality)) => render_equality_across_representative(
            equality,
            &source_body,
            &target_body,
            source_value,
            target_value,
            source_same_target,
            "__transport_body",
        )?,
        _ => render_fact_proof_across_exact_predicate_arguments(
            &body,
            &body,
            &source_body,
            &target_body,
            "__transport_body",
        )?,
    };
    Ok(format!(
        "(by\n  rcases ({source_proof}) with ⟨{witness}, {membership}, __transport_body⟩\n  exact ⟨{witness}, {membership}, {transported_body}⟩)"
    ))
}

/// Transport one zero-ended sign proposition from the source value used to
/// check a set-builder clause to the exact base-carrier representative used by
/// the Lean set-builder predicate. General binary order is deliberately not
/// transported here: its two observations need a separate reviewed ABI.
pub(in super::super) fn render_zero_ended_order_across_representative(
    fact: &Fact,
    source: &StmtResultToLeanCompilerEnvironmentStack,
    target: &StmtResultToLeanCompilerEnvironmentStack,
    source_value: &str,
    target_value: &str,
    source_same_target: &str,
    source_proof: &str,
) -> Result<String, String> {
    let (left, right, strict) = order_relation_parts(fact)?;
    let source_left = render_obj(left, source)?;
    let source_right = render_obj(right, source)?;
    let target_left = render_obj(left, target)?;
    let target_right = render_obj(right, target)?;
    let left_changed = source_left == source_value && target_left == target_value;
    let right_changed = source_right == source_value && target_right == target_value;

    let predicate = if is_literal_zero(left) && right_changed && source_left == target_left {
        if strict {
            "Litex.Positive"
        } else {
            "Litex.Nonnegative"
        }
    } else if is_literal_zero(right) && left_changed && source_right == target_right {
        if strict {
            "Litex.Negative"
        } else {
            "Litex.Nonpositive"
        }
    } else if !left_changed
        && !right_changed
        && render_fact(fact, source)? == render_fact(fact, target)?
    {
        return Ok(source_proof.to_string());
    } else {
        return Err(
            "compiler set-builder order transport requires the changing value as the nonzero side of a zero-ended comparison"
                .into(),
        );
    };

    Ok(format!(
        "({predicate}.congr ({source_same_target})).mp ({source_proof})"
    ))
}
