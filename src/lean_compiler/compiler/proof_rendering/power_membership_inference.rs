//! Membership transport across positive power equalities.

use super::super::*;

/// Replay the verifier's exact positive-power equality transport. The rule is
/// intentionally limited to a closed power whose positive value is checked
/// again here; equality orientation and the `R+` target must match the retained
/// certificate exactly.
pub(in super::super) fn render_closed_positive_power_equality_membership_inference(
    rule: &ClosedPositivePowerEqualityImpliesEqualSideMembershipInferRule,
    source: &Fact,
    target: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source else {
        return Err("closed-positive-power inference premise is not equality".into());
    };
    let (power, opposite) = if rule.power_is_left_endpoint {
        (&equality.left, &equality.right)
    } else {
        (&equality.right, &equality.left)
    };
    if !matches!(power, Obj::Pow(_)) {
        return Err("closed-positive-power inference selected a non-power endpoint".into());
    }
    let evaluation = power
        .evaluate_to_normalized_decimal_number()
        .ok_or_else(|| {
            "closed-positive-power inference endpoint no longer evaluates".to_string()
        })?;
    if !matches!(
        compare_normalized_number_str_to_zero(&evaluation.normalized_value),
        NumberCompareResult::Greater
    ) {
        return Err("closed-positive-power inference endpoint is not positive".into());
    }
    let (target_element, target_set) = membership_parts(target)?;
    if obj_equality_key(target_element) != obj_equality_key(opposite)
        || !matches!(target_set, Obj::StandardSet(StandardSet::RPos))
    {
        return Err(
            "closed-positive-power inference changed its opposite endpoint or R+ target".into(),
        );
    }

    let rendered_power = render_obj(power, context)?;
    let rendered_set = render_obj(target_set, context)?;
    let normalized = &evaluation.normalized_value;
    let power_membership = format!(
        "Litex.Rules.complexEqRealInRPos {rendered_power} ({normalized} : ℝ) (by norm_num) (by norm_num)"
    );
    let direction = if rule.power_is_left_endpoint {
        "mp"
    } else {
        "mpr"
    };
    Ok(format!(
        "(Litex.In.congr ({source_proof}) {rendered_set}).{direction} ({power_membership})"
    ))
}

/// Replay positive `Z`-base power membership through one exact equality. The
/// integer representation is selected by the cited `Z` premise, while the
/// cited strict-order premise supplies the Mathlib positivity proof.
pub(in super::super) fn render_positive_integer_base_natural_power_equality_membership_inference(
    rule: &PositiveIntegerBaseNaturalPowerEqualityImpliesEqualSideMembershipInferRule,
    source: &Fact,
    base_positive: &Fact,
    base_in_z: &Fact,
    source_proof: &str,
    base_positive_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<(Fact, String), String> {
    let Fact::AtomicFact(AtomicFact::EqualFact(equality)) = source else {
        return Err("positive-integer-power inference premise is not equality".into());
    };
    let (power_object, opposite) = if rule.power_is_left_endpoint {
        (&equality.left, &equality.right)
    } else {
        (&equality.right, &equality.left)
    };
    let Obj::Pow(power) = power_object else {
        return Err("positive-integer-power inference selected a non-power endpoint".into());
    };
    let exponent = power
        .exponent
        .evaluate_to_normalized_decimal_number()
        .and_then(|number| number.normalized_value.parse::<i128>().ok())
        .filter(|exponent| *exponent >= 0)
        .ok_or_else(|| {
            "positive-integer-power inference exponent is not a closed natural".to_string()
        })?;
    let (positive_left, positive_right, positive_strict) = order_relation_parts(base_positive)?;
    if !positive_strict
        || !is_literal_zero(positive_left)
        || obj_equality_key(positive_right) != obj_equality_key(power.base.as_ref())
    {
        return Err("positive-integer-power inference changed its base positivity premise".into());
    }
    let (membership_element, membership_set) = membership_parts(base_in_z)?;
    if obj_equality_key(membership_element) != obj_equality_key(power.base.as_ref())
        || !matches!(membership_set, Obj::StandardSet(StandardSet::Z))
    {
        return Err("positive-integer-power inference changed its base Z premise".into());
    }

    let rendered_base = render_integer_obj(power.base.as_ref(), context)?;
    let rendered_set = render_obj(&Obj::from(StandardSet::RPos), context)?;
    let power_membership = format!(
        "Litex.Rules.positiveIntegerRationalPowInRPos ({rendered_base}) ({exponent} : ℤ) ({base_positive_proof}) (by norm_num)"
    );
    let direction = if rule.power_is_left_endpoint {
        "mp"
    } else {
        "mpr"
    };
    let target: Fact = InFact::new(
        opposite.clone(),
        StandardSet::RPos.into(),
        source.line_file(),
    )
    .into();
    Ok((
        target,
        format!(
            "(Litex.In.congr ({source_proof}) {rendered_set}).{direction} ({power_membership})"
        ),
    ))
}
