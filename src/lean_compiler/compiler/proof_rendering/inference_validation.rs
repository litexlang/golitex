//! Typed inference target validation.

use super::super::*;

pub(in super::super) fn validate_order_sign_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (source_left, source_right, source_strict) = order_relation_parts(source)?;
    let (target_left, target_right, target_strict) = order_relation_parts(target)?;
    let zero =
        |object: &Obj| matches!(object, Obj::Number(number) if number.normalized_value == "0");
    match rule {
        InferRule::MultiplicationByNegativeOneReversesOrderAgainstZero => {
            let (source_expression, source_expression_is_left) = if zero(source_right) {
                (source_left, true)
            } else if zero(source_left) {
                (source_right, false)
            } else {
                return Err("negative-one order inference source is not compared with zero".into());
            };
            let (target_expression, target_expression_is_left) = if zero(target_right) {
                (target_left, true)
            } else if zero(target_left) {
                (target_right, false)
            } else {
                return Err("negative-one order inference target is not compared with zero".into());
            };
            let Obj::Mul(multiplication) = target_expression else {
                return Err("negative-one order inference target is not a multiplication".into());
            };
            if !matches!(multiplication.left.as_ref(), Obj::Number(number) if number.normalized_value == "-1")
                || obj_equality_key(multiplication.right.as_ref())
                    != obj_equality_key(source_expression)
                || source_expression_is_left == target_expression_is_left
            {
                return Err(
                    "negative-one order inference changed its operand or reversal orientation"
                        .into(),
                );
            }
            let expected_target_strict = source_strict && !source_expression_is_left;
            if target_strict != expected_target_strict {
                return Err("negative-one order inference changed its strictness contract".into());
            }
            Ok(())
        }
        InferRule::StrictOrderComparedToZeroImpliesWeakOrder => {
            if !source_strict
                || target_strict
                || obj_equality_key(source_left) != obj_equality_key(target_left)
                || obj_equality_key(source_right) != obj_equality_key(target_right)
                || !zero(source_right)
            {
                return Err("strict-to-weak zero-order inference changed its endpoints".into());
            }
            Ok(())
        }
        _ => Err("non-order inference reached order-sign validation".into()),
    }
}

/// Replay the verifier's bounded-sign accelerator using only the cited order
/// premise plus a closed numeric comparison proved by Mathlib. The source and
/// target are normalized to left-to-right order before their exact endpoint
/// shape is checked.
pub(in super::super) fn render_numeric_order_bound_implies_zero_sign_inference(
    source: &Fact,
    target: &Fact,
    source_proof: &str,
    _context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (source_left, source_right, source_strict) = order_relation_parts(source)?;
    let (target_left, target_right, target_strict) = order_relation_parts(target)?;
    let zero = |object: &Obj| is_literal_zero(object);

    if target_strict
        && zero(target_left)
        && obj_equality_key(target_right) == obj_equality_key(source_right)
    {
        let Obj::Number(bound) = source_left else {
            return Err(
                "numeric-bound sign inference requires a literal positive lower bound in Lean"
                    .into(),
            );
        };
        if !matches!(
            compare_normalized_number_str_to_zero(&bound.normalized_value),
            NumberCompareResult::Greater
        ) {
            return Err("numeric-bound sign inference changed its positive lower bound".into());
        }
        let numeric_proof = format!(
            "Litex.OrderBridge.ltOfComplexReals (show (0 : ℝ) < ({} : ℝ) by norm_num)",
            bound.normalized_value
        );
        return Ok(if source_strict {
            format!("Litex.Lt.trans ({numeric_proof}) ({source_proof})")
        } else {
            format!("Litex.Lt.transLe ({numeric_proof}) ({source_proof})")
        });
    }

    if !target_strict
        && zero(target_right)
        && obj_equality_key(target_left) == obj_equality_key(source_left)
    {
        let Obj::Number(bound) = source_right else {
            return Err(
                "numeric-bound sign inference requires a literal nonpositive upper bound in Lean"
                    .into(),
            );
        };
        return match compare_normalized_number_str_to_zero(&bound.normalized_value) {
            NumberCompareResult::Equal if source_strict => {
                Ok(format!("Litex.Lt.toLe ({source_proof})"))
            }
            NumberCompareResult::Less => {
                let numeric_proof = format!(
                    "Litex.OrderBridge.ltOfComplexReals (show ({} : ℝ) < (0 : ℝ) by norm_num)",
                    bound.normalized_value
                );
                let strict_proof = if source_strict {
                    format!("Litex.Lt.trans ({source_proof}) ({numeric_proof})")
                } else {
                    format!("Litex.Le.transLt ({source_proof}) ({numeric_proof})")
                };
                Ok(format!("Litex.Lt.toLe ({strict_proof})"))
            }
            _ => Err("numeric-bound sign inference changed its nonpositive upper bound".into()),
        };
    }

    Err("numeric-bound sign inference changed its zero-ended target".into())
}

pub(in super::super) fn validate_membership_in_equal_set_inference_target(
    rule: &MembershipInSetWithKnownEqualityImpliesMembershipInEqualSetInferRule,
    source: &Fact,
    equality: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (source_element, source_set) = membership_parts(source)?;
    let (target_element, target_set) = membership_parts(target)?;
    let (equality_left, equality_right) = equality_parts(equality)?;
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("equal-set membership inference changed its element".into());
    }
    let (expected_left, expected_right) = match rule.equality_orientation {
        KnownSetEqualityOrientation::SourceSetOnLeft => (source_set, target_set),
        KnownSetEqualityOrientation::SourceSetOnRight => (target_set, source_set),
    };
    if obj_equality_key(equality_left) != obj_equality_key(expected_left)
        || obj_equality_key(equality_right) != obj_equality_key(expected_right)
    {
        return Err("equal-set membership inference changed its retained equality".into());
    }
    Ok(())
}

pub(in super::super) fn validate_set_inclusion_elementwise_forall_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let (expected_parameter_set, expected_target_set, binder_symbol_id) = match (rule, source) {
        (
            InferRule::SubsetImpliesElementwiseMembershipForall(rule),
            Fact::AtomicFact(AtomicFact::SubsetFact(source)),
        ) => (&source.left, &source.right, rule.binder_symbol_id),
        (
            InferRule::SupersetImpliesElementwiseMembershipForall(rule),
            Fact::AtomicFact(AtomicFact::SupersetFact(source)),
        ) => (&source.right, &source.left, rule.binder_symbol_id),
        (InferRule::SubsetImpliesElementwiseMembershipForall(_), _) => {
            return Err("subset elementwise inference retained a non-subset premise".into());
        }
        (InferRule::SupersetImpliesElementwiseMembershipForall(_), _) => {
            return Err("superset elementwise inference retained a non-superset premise".into());
        }
        _ => return Err("non-inclusion inference reached elementwise-forall validation".into()),
    };
    let Fact::ForallFact(target) = target else {
        return Err("set-inclusion inference conclusion is not a forall fact".into());
    };
    let [parameter_group] = target.typed_parameters.groups.as_slice() else {
        return Err("set-inclusion inference conclusion changed its parameter-group arity".into());
    };
    let [parameter] = parameter_group.params.as_slice() else {
        return Err("set-inclusion inference conclusion changed its binder arity".into());
    };
    let ParamType::Obj(parameter_set) = &parameter_group.param_type else {
        return Err("set-inclusion inference conclusion binder is not object-valued".into());
    };
    if parameter.id() != binder_symbol_id
        || obj_equality_key(parameter_set) != obj_equality_key(expected_parameter_set)
        || !target.dom_facts.is_empty()
        || target.then_facts.len() != 1
    {
        return Err(
            "set-inclusion inference changed its binder identity, carrier, or forall shape".into(),
        );
    }
    let target_membership = target.then_facts[0].clone().to_fact();
    let (target_element, target_set) = membership_parts(&target_membership)?;
    let expected_element = obj_for_bound_param_in_scope(parameter);
    if obj_equality_key(target_element) != obj_equality_key(&expected_element)
        || obj_equality_key(target_set) != obj_equality_key(expected_target_set)
    {
        return Err("set-inclusion inference changed its elementwise membership target".into());
    }
    Ok(())
}

pub(in super::super) fn elementwise_forall_is_set_inclusion(
    candidate: &Fact,
    inclusion: &Fact,
) -> bool {
    let Fact::ForallFact(candidate) = candidate else {
        return false;
    };
    let Ok((expected_parameter_set, expected_target_set)) = subset_parts(inclusion) else {
        return false;
    };
    let [parameter_group] = candidate.typed_parameters.groups.as_slice() else {
        return false;
    };
    let [parameter] = parameter_group.params.as_slice() else {
        return false;
    };
    let ParamType::Obj(parameter_set) = &parameter_group.param_type else {
        return false;
    };
    if obj_equality_key(parameter_set) != obj_equality_key(expected_parameter_set)
        || !candidate.dom_facts.is_empty()
        || candidate.then_facts.len() != 1
    {
        return false;
    }
    let target_membership = candidate.then_facts[0].clone().to_fact();
    let Ok((target_element, target_set)) = membership_parts(&target_membership) else {
        return false;
    };
    let expected_element = obj_for_bound_param_in_scope(parameter);
    obj_equality_key(target_element) == obj_equality_key(&expected_element)
        && obj_equality_key(target_set) == obj_equality_key(expected_target_set)
}

pub(in super::super) fn validate_conjunction_component_inference_target(
    rule: &ConjunctionImpliesComponentInferRule,
    source: &Fact,
    target: &Fact,
) -> Result<(), String> {
    let Fact::AndFact(source) = source else {
        return Err("conjunction-component inference retained a non-conjunction premise".into());
    };
    if rule.component_count != source.facts.len() || rule.component_index >= rule.component_count {
        return Err("conjunction-component inference changed its component bounds".into());
    }
    let expected: Fact = source.facts[rule.component_index].clone().into();
    if expected.to_string() != target.to_string() {
        return Err("conjunction-component inference changed its selected component".into());
    }
    Ok(())
}

pub(in super::super) fn validate_standard_numeric_membership_inference_target(
    rule: &InferRule,
    source: &Fact,
    target: &Fact,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<&'static str, String> {
    let (source_element, source_set) = membership_parts(source)?;
    let (target_element, lean_theorem_name) = match rule {
        InferRule::NaturalMembershipImpliesNonnegative => {
            if !matches!(source_set, Obj::StandardSet(StandardSet::N)) {
                return Err("natural-membership inference source is not in N".into());
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::GreaterEqualFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                Fact::AtomicFact(AtomicFact::LessEqualFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                _ => {
                    return Err(
                        "natural-membership inference target is not nonnegativity of its source object"
                            .into(),
                    );
                }
            };
            let semantic_target =
                format!("Litex.Nonnegative {}", render_obj(target_element, context)?);
            let theorem = if render_fact(target, context)? == semantic_target {
                "nonnegativeOfInN"
            } else {
                "naturalRepNonnegative"
            };
            (target_element, theorem)
        }
        InferRule::PositiveStandardSetMembershipImpliesPositive(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "positive-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::LessFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                Fact::AtomicFact(AtomicFact::GreaterFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                _ => {
                    return Err(
                        "positive-carrier inference target is not strict positivity of its source object"
                            .into(),
                    );
                }
            };
            let semantic_target =
                format!("Litex.Positive {}", render_obj(target_element, context)?);
            let semantic = render_fact(target, context)? == semantic_target;
            let exact_positive_real_carrier = matches!(
                LeanTargetObjectRepresentation::lower(source_element),
                Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. })
                    if context.exact_positive_real_carriers.contains_key(&symbol_id)
            );
            let lean_theorem_name = match (rule.source_set, semantic) {
                (StandardSet::NPos, true) => "positiveOfInNPos",
                (StandardSet::QPos, true) => "positiveOfInQPos",
                (StandardSet::RPos, true) => "positiveOfInRPos",
                (StandardSet::NPos, false) => "positiveNaturalRepPositive",
                (StandardSet::QPos, false) => "positiveRationalRepPositive",
                (StandardSet::RPos, false) if exact_positive_real_carrier => {
                    "positiveRealCarrierPositive"
                }
                (StandardSet::RPos, false) => "positiveRealRepPositive",
                _ => {
                    return Err(format!(
                        "positive-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        InferRule::NegativeStandardSetMembershipImpliesNegative(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "negative-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::LessFact(order)) if matches!(&order.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.left
                }
                Fact::AtomicFact(AtomicFact::GreaterFact(order)) if matches!(&order.left, Obj::Number(number) if number.normalized_value == "0") => {
                    &order.right
                }
                _ => {
                    return Err(
                        "negative-carrier inference target is not strict negativity of its source object"
                            .into(),
                    );
                }
            };
            let semantic_target =
                format!("Litex.Negative {}", render_obj(target_element, context)?);
            let semantic = render_fact(target, context)? == semantic_target;
            let lean_theorem_name = match (rule.source_set, semantic) {
                (StandardSet::ZNeg, true) => "negativeOfInZNeg",
                (StandardSet::QNeg, true) => "negativeOfInQNeg",
                (StandardSet::RNeg, true) => "negativeOfInRNeg",
                (StandardSet::ZNeg, false) => "negativeIntegerRepNegative",
                (StandardSet::QNeg, false) => "negativeRationalRepNegative",
                (StandardSet::RNeg, false) => "negativeRealRepNegative",
                _ => {
                    return Err(format!(
                        "negative-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        InferRule::NonzeroStandardSetMembershipImpliesNonzero(rule) => {
            if !matches!(source_set, Obj::StandardSet(set) if *set == rule.source_set) {
                return Err(
                    "nonzero-carrier inference source does not match its typed source set".into(),
                );
            }
            let target_element = match target {
                Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal)) if matches!(&not_equal.right, Obj::Number(number) if number.normalized_value == "0") => {
                    &not_equal.left
                }
                _ => {
                    return Err(
                        "nonzero-carrier inference target is not source-object inequality with zero"
                            .into(),
                    );
                }
            };
            let lean_theorem_name = match rule.source_set {
                StandardSet::ZStar => "notSameZeroOfInZStar",
                StandardSet::QStar => "notSameZeroOfInQStar",
                StandardSet::RStar => "notSameZeroOfInRStar",
                StandardSet::CStar => "notSameZeroOfInCStar",
                _ => {
                    return Err(format!(
                        "nonzero-carrier inference from {} has no direct Lean theorem",
                        rule.source_set
                    ));
                }
            };
            (target_element, lean_theorem_name)
        }
        _ => return Err("unsupported standard numeric inference rule".into()),
    };
    if obj_equality_key(source_element) != obj_equality_key(target_element) {
        return Err("standard numeric inference changed its source object".into());
    }
    Ok(lean_theorem_name)
}
