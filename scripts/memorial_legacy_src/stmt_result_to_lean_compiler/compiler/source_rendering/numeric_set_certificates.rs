//! Exact-set and membership numeric values, equalities, and proofs.

use super::super::*;

/// Recover the exact positive-natural carrier selected by a closed membership
/// certificate. This walks only explicit proof sharing; an arbitrary `In`
/// proof deliberately exposes no observed numeric representative.
pub(in super::super) fn closed_positive_natural_value_from_fact_proof(
    proof: &SuccessFactProofNode,
) -> Result<Option<String>, String> {
    match proof.proof() {
        SuccessFactProofResult::BuiltinRule(builtin)
        | SuccessFactProofResult::BuiltinStrategy(builtin) => {
            let Some(BuiltinRuleEvidence::ClosedNumericMembership(evidence)) =
                builtin.evidence.typed()
            else {
                return Ok(None);
            };
            if evidence.target_set != StandardSet::NPos
                || evidence.expected_target.to_string() != proof.fact().to_string()
            {
                return Ok(None);
            }
            validate_success_evaluate_obj_result(&evidence.evaluation)?;
            let value = &evidence.evaluation.value.normalized_value;
            if value.chars().all(|character| character.is_ascii_digit())
                && value.chars().any(|character| character != '0')
            {
                Ok(Some(value.clone()))
            } else {
                Err(format!(
                    "positive-natural membership retained invalid normalized value `{value}`"
                ))
            }
        }
        SuccessFactProofResult::Reuse(reuse) => {
            closed_positive_natural_value_from_fact_proof(reuse.source.as_ref())
        }
        _ => Ok(None),
    }
}

pub(in super::super) fn exact_set_real_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("(({value} : ℤ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("(({value} : ℚ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveRational | LeanTargetStandardSet::NegativeRational,
        ) => Some(format!("((({value}).val : ℚ) : ℝ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("((({value}).val : ℤ) : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveReal | LeanTargetStandardSet::NegativeReal,
        ) => Some(format!("(({value}).val : ℝ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("({value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_real_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(in super::super) fn exact_set_integer_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("((({value}).val : ℕ) : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("({value} : ℤ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("(({value}).val : ℤ)"))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => {
            Some(format!("(({value}).val : ℤ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_integer_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(in super::super) fn exact_set_rational_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("((({value}).val : ℕ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("(({value} : ℕ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("(({value} : ℤ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("({value} : ℚ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(
            LeanTargetStandardSet::PositiveRational | LeanTargetStandardSet::NegativeRational,
        ) => Some(format!("(({value}).val : ℚ)")),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("((({value}).val : ℤ) : ℚ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_rational_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(in super::super) fn exact_set_numeric_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!("(((({value}).val : ℕ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("((({value} : ℕ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("((({value} : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("((({value} : ℚ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("((({value} : ℝ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(value.to_string())
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!("(((({value}).val : ℚ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!("(((({value}).val : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => {
            Some(format!("(((({value}).val : ℤ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!("(((({value}).val : ℝ)) : ℂ)"))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_numeric_value(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}

pub(in super::super) fn membership_real_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_real_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(in super::super) fn membership_integer_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_integer_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(in super::super) fn membership_rational_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    exact_set_rational_value(set, &format!("Litex.In.rep {value} {membership}"))
}

pub(in super::super) fn membership_numeric_value(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    // A forall-bound Litex object can use any host carrier, including when its
    // checked set is `C`.  Arithmetic therefore observes the exact carrier
    // representative selected by the retained membership proof.  For an
    // already-exact carrier `In.rep_exact` reduces this back to `value`.
    exact_set_numeric_value(set, &format!("Litex.In.rep {value} {membership}"))
}

/// Construct the exact `Same source selected_numeric_complex_value` bridge
/// owned by one visible membership proof. This is target representation state,
/// not a new proof search: every step is determined by the carrier and the
/// same `Litex.In.rep` expression used by `membership_numeric_value`.
pub(in super::super) fn membership_numeric_equality(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    let representative = format!("Litex.In.rep {value} {membership}");
    if matches!(
        set,
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex)
    ) {
        // Generic `In` stores no-observation equality. It cannot be upgraded
        // to the complex observer merely because its selected carrier reduces
        // to `Complex`. Exact `C` binders use `exact_set_numeric_equality`;
        // truly heterogeneous `C` values therefore stay without a numeric
        // equality bridge and unsupported consumers fail closed.
        return None;
    }
    let representative_to_numeric =
        exact_set_numeric_equality_no_observation(set, &representative)?;
    Some(format!(
        "Litex.Same.transNoObservation (Litex.In.same_rep {value} ({membership})) ({representative_to_numeric})"
    ))
}

pub(in super::super) fn exact_set_numeric_equality_no_observation(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!(
                "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) (Litex.Same.natComplexNoObservation (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("Litex.Same.natComplexNoObservation ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("Litex.Same.intComplexNoObservation ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("Litex.Same.ratComplexNoObservation ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("Litex.Same.realComplexNoObservation ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("Litex.Same.reflNoObservation ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!(
                "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) (Litex.Same.ratComplexNoObservation (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!(
                "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) (Litex.Same.intComplexNoObservation (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => Some(format!(
            "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) (Litex.Same.intComplexNoObservation (({value}).val))"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!(
                "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) (Litex.Same.realComplexNoObservation (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            let base_value = format!("({value}).val");
            let base_equality =
                exact_set_numeric_equality_no_observation(builder.set.as_ref(), &base_value)?;
            Some(format!(
                "Litex.Same.transNoObservation (Litex.Same.subtypeNoObservation ({value})) ({base_equality})"
            ))
        }
        _ => None,
    }
}

pub(in super::super) fn exact_set_numeric_equality(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.natComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => {
            Some(format!("Litex.Same.natComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => {
            Some(format!("Litex.Same.intComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => {
            Some(format!("Litex.Same.ratComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("Litex.Same.realComplex ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("Litex.Same.refl ({value})"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.ratComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.intComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => Some(format!(
            "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.intComplex (({value}).val))"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal)
        | LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) (Litex.Same.realComplex (({value}).val))"
            ))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            let base_value = format!("({value}).val");
            let base_equality = exact_set_numeric_equality(builder.set.as_ref(), &base_value)?;
            Some(format!(
                "Litex.Same.trans (Litex.Same.subtype ({value})) ({base_equality})"
            ))
        }
        _ => None,
    }
}

pub(in super::super) fn membership_numeric_proof(
    set: &LeanTargetObjectRepresentation,
    value: &str,
    membership: &str,
) -> Option<String> {
    let representative = format!("Litex.In.rep {value} {membership}");
    exact_set_numeric_proof(set, &representative)
}

pub(in super::super) fn exact_set_numeric_proof(
    set: &LeanTargetObjectRepresentation,
    value: &str,
) -> Option<String> {
    match set {
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveNatural) => {
            Some(format!(
                "Litex.Rules.complexEqNatInNPos (((({value}).val : ℕ) : ℂ)) (({value}).val : ℕ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Natural) => Some(format!(
            "Litex.Rules.complexEqNatInN ((({value} : ℕ) : ℂ)) ({value} : ℕ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Integer) => Some(format!(
            "Litex.Rules.complexEqIntInZ ((({value} : ℤ) : ℂ)) ({value} : ℤ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Rational) => Some(format!(
            "Litex.Rules.complexEqRatInQ ((({value} : ℚ) : ℂ)) ({value} : ℚ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Real) => {
            Some(format!("Litex.Rules.complexRealInR ({value} : ℝ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::Complex) => {
            Some(format!("Litex.Rules.complexInC ({value} : ℂ)"))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveRational) => {
            Some(format!(
                "Litex.Rules.complexEqRatInQPos (((({value}).val : ℚ) : ℂ)) (({value}).val : ℚ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeInteger) => {
            Some(format!(
                "Litex.Rules.complexEqIntInZNeg (((({value}).val : ℤ) : ℂ)) (({value}).val : ℤ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::Range { .. }
        | LeanTargetObjectRepresentation::ClosedRange { .. } => Some(format!(
            "Litex.Rules.complexEqIntInZ (((({value}).val : ℤ) : ℂ)) (({value}).val : ℤ) (by rfl)"
        )),
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeRational) => {
            Some(format!(
                "Litex.Rules.complexEqRatInQNeg (((({value}).val : ℚ) : ℂ)) (({value}).val : ℚ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::PositiveReal) => {
            Some(format!(
                "Litex.Rules.complexEqRealInRPos (((({value}).val : ℝ) : ℂ)) (({value}).val : ℝ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::StandardSet(LeanTargetStandardSet::NegativeReal) => {
            Some(format!(
                "Litex.Rules.complexEqRealInRNeg (((({value}).val : ℝ) : ℂ)) (({value}).val : ℝ) (by rfl) (({value}).property)"
            ))
        }
        LeanTargetObjectRepresentation::SetBuilder(builder) => {
            exact_set_numeric_proof(builder.set.as_ref(), &format!("({value}).val"))
        }
        _ => None,
    }
}
