//! Closed numeric comparison rendering and evidence validation.

use super::super::*;

pub(in super::super) fn render_closed_numeric_comparison_fact(
    fact: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if !fact_is_closed_numeric_relation(fact) {
        return Err("closed numeric comparison changed its target".into());
    }
    let (left, right, theorem, _strict, negated) = match fact {
        Fact::AtomicFact(AtomicFact::LessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, false)
        }
        Fact::AtomicFact(AtomicFact::LessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, false)
        }
        Fact::AtomicFact(AtomicFact::NotLessFact(order)) => {
            (&order.left, &order.right, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterFact(order)) => {
            (&order.right, &order.left, "ltOfComplexReals", true, true)
        }
        Fact::AtomicFact(AtomicFact::NotLessEqualFact(order)) => {
            (&order.left, &order.right, "leOfComplexReals", false, true)
        }
        Fact::AtomicFact(AtomicFact::NotGreaterEqualFact(order)) => {
            (&order.right, &order.left, "leOfComplexReals", false, true)
        }
        _ => {
            return Err(
                "compiler closed comparison requires an order relation; closed equality and disequality use separate semantic adapters"
                    .into()
            )
        }
    };
    render_obj(left, context)?;
    render_obj(right, context)?;
    if negated {
        return Ok("(by\n  norm_num [Litex.Lt, Litex.Le, Litex.OrderValue])".into());
    }
    if is_literal_zero(left) {
        let Obj::Number(number) = right else {
            return Err(
                "closed zero-ended positive comparison currently requires a literal nonzero endpoint"
                    .into(),
            );
        };
        let constructor = if theorem == "ltOfComplexReals" {
            "positiveOfComplexReal"
        } else {
            "nonnegativeOfComplexReal"
        };
        return Ok(format!(
            "Litex.OrderBridge.{constructor} (show (0 : ℝ) {} ({} : ℝ) by norm_num)",
            if theorem == "ltOfComplexReals" {
                "<"
            } else {
                "≤"
            },
            number.normalized_value,
        ));
    }
    if is_literal_zero(right) {
        let Obj::Number(number) = left else {
            return Err(
                "closed zero-ended negative comparison currently requires a literal nonzero endpoint"
                    .into(),
            );
        };
        let predicate = if theorem == "ltOfComplexReals" {
            "Negative"
        } else {
            "Nonpositive"
        };
        return Ok(format!(
            "Litex.{predicate}.intro (Litex.AsReal.complex ({} : ℝ)) (show ({} : ℝ) {} 0 by norm_num)",
            number.normalized_value,
            number.normalized_value,
            if theorem == "ltOfComplexReals" { "<" } else { "≤" },
        ));
    }
    let rendered_left = render_numeric_obj(left, context)?;
    let rendered_right = render_numeric_obj(right, context)?;
    let rendered_relation = if theorem == "ltOfComplexReals" {
        format!("Litex.Lt ({rendered_left}) ({rendered_right})")
    } else {
        format!("Litex.Le ({rendered_left}) ({rendered_right})")
    };
    Ok(format!(
        "(Litex.OrderBridge.{theorem} (by norm_num) : {rendered_relation})"
    ))
}

pub(in super::super) fn render_closed_numeric_comparison_fact_from_result(
    fact: &Fact,
    evidence: &ClosedNumericComparisonBuiltinRuleEvidence,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let Fact::AtomicFact(atomic) = fact else {
        return Err("closed numeric comparison evidence targets a non-atomic fact".into());
    };
    let (left, right, strict, negated) = match atomic {
        AtomicFact::LessFact(order) => (&order.left, &order.right, true, false),
        AtomicFact::GreaterFact(order) => (&order.right, &order.left, true, false),
        AtomicFact::LessEqualFact(order) => (&order.left, &order.right, false, false),
        AtomicFact::GreaterEqualFact(order) => (&order.right, &order.left, false, false),
        AtomicFact::NotLessFact(order) => (&order.left, &order.right, true, true),
        AtomicFact::NotGreaterFact(order) => (&order.right, &order.left, true, true),
        AtomicFact::NotLessEqualFact(order) => (&order.left, &order.right, false, true),
        AtomicFact::NotGreaterEqualFact(order) => (&order.right, &order.left, false, true),
        AtomicFact::NotEqualFact(_) => {
            return render_closed_numeric_comparison_fact(fact, context);
        }
        _ => return Err("closed numeric comparison evidence changed its relation".into()),
    };
    if negated {
        return render_closed_numeric_comparison_fact(fact, context);
    }
    let normalized_endpoint = |endpoint: &Obj| -> Result<&str, String> {
        [&evidence.left_evaluation, &evidence.right_evaluation]
            .into_iter()
            .find(|evaluation| {
                obj_equality_key(&evaluation.expression) == obj_equality_key(endpoint)
            })
            .map(|evaluation| evaluation.value.normalized_value.as_str())
            .ok_or_else(|| {
                "closed numeric comparison evidence lost a zero-ended endpoint".to_string()
            })
    };
    if is_literal_zero(left) && !matches!(right, Obj::Number(_)) {
        let source = render_numeric_obj(right, context)?;
        let normalized = normalized_endpoint(right)?;
        let theorem = if strict {
            "complexEqRealPositive"
        } else {
            "complexEqRealNonnegative"
        };
        return Ok(format!(
            "Litex.Rules.{theorem} ({source}) ({normalized} : ℝ) (by norm_num) (by norm_num)"
        ));
    }
    if is_literal_zero(right) && !matches!(left, Obj::Number(_)) {
        let source = render_numeric_obj(left, context)?;
        let normalized = normalized_endpoint(left)?;
        let theorem = if strict {
            "complexEqRealNegative"
        } else {
            "complexEqRealNonpositive"
        };
        return Ok(format!(
            "Litex.Rules.{theorem} ({source}) ({normalized} : ℝ) (by norm_num) (by norm_num)"
        ));
    }
    render_closed_numeric_comparison_fact(fact, context)
}

pub(in super::super) fn validate_closed_numeric_comparison_builtin_rule_evidence(
    source_fact: &Fact,
    evidence: &ClosedNumericComparisonBuiltinRuleEvidence,
) -> Result<(), String> {
    if evidence.expected_target.to_string() != source_fact.to_string() {
        return Err("closed-numeric-comparison evidence changed its target".into());
    }
    validate_success_evaluate_obj_result(&evidence.left_evaluation)?;
    validate_success_evaluate_obj_result(&evidence.right_evaluation)?;

    let Fact::AtomicFact(source_atomic_fact) = source_fact else {
        return Err("closed-numeric-comparison evidence targets a non-atomic fact".into());
    };
    if let AtomicFact::NotEqualFact(not_equal) = source_atomic_fact {
        if obj_equality_key(&not_equal.left)
            != obj_equality_key(&evidence.left_evaluation.expression)
            || obj_equality_key(&not_equal.right)
                != obj_equality_key(&evidence.right_evaluation.expression)
        {
            return Err("closed numeric disequality changed an endpoint".into());
        }
        if evidence.left_evaluation.value.normalized_value
            == evidence.right_evaluation.value.normalized_value
        {
            return Err("closed numeric disequality retained equal normal forms".into());
        }
        return Ok(());
    }

    let Some((normalized_left, normalized_right, allow_equal)) =
        normalized_positive_order_operands(source_atomic_fact)
    else {
        return Err("closed numeric comparison retained a non-comparison target".into());
    };
    if obj_equality_key(normalized_left) != obj_equality_key(&evidence.left_evaluation.expression)
        || obj_equality_key(normalized_right)
            != obj_equality_key(&evidence.right_evaluation.expression)
    {
        return Err("closed numeric comparison changed a normalized endpoint".into());
    }
    let comparison = crate::verification::compare_number_strings(
        &evidence.left_evaluation.value.normalized_value,
        &evidence.right_evaluation.value.normalized_value,
    );
    let comparison_holds = matches!(comparison, crate::verification::NumberCompareResult::Less)
        || (allow_equal && matches!(comparison, crate::verification::NumberCompareResult::Equal));
    if !comparison_holds {
        return Err("closed numeric comparison retained a false normalized relation".into());
    }
    Ok(())
}
