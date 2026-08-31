//! Numeric operand membership and sign-rule proof rendering.

use super::super::*;

pub(in super::super) fn render_numeric_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    let proof = match LeanTargetObjectRepresentation::lower(object) {
        Ok(LeanTargetObjectRepresentation::Symbol { symbol_id, .. }) => {
            context.numeric_representation_memberships.get(&symbol_id)
        }
        _ => None,
    };
    proof.map_or_else(|| fallback.to_string(), Clone::clone)
}

pub(in super::super) fn render_additive_sign_rule_from_compiled_children(
    fact: &Fact,
    rule: LeanArithmeticBuiltinCompilationKind,
    premises: &[CompiledFactProofBody],
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if premises.len() != 2 {
        return Err("additive sign rule requires two ordered child Results".into());
    }
    let (target_is_strict, left_is_strict, right_is_strict, theorem) = match rule {
        LeanArithmeticBuiltinCompilationKind::AddNonnegative => {
            (false, false, false, "complexAddNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositive => {
            (true, true, true, "complexAddPositive")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict => {
            (true, true, false, "complexAddPositiveLeftStrict")
        }
        LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict => {
            (true, false, true, "complexAddPositiveRightStrict")
        }
        LeanArithmeticBuiltinCompilationKind::MulNonnegative => {
            (false, false, false, "complexMulNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::MulPositive => {
            (true, true, true, "complexMulPositive")
        }
        LeanArithmeticBuiltinCompilationKind::DivNonnegative => {
            (false, false, true, "complexDivNonnegative")
        }
        LeanArithmeticBuiltinCompilationKind::DivPositive => {
            (true, true, true, "complexDivPositive")
        }
    };

    let (target_zero, target_expression) = positive_order_parts(fact, target_is_strict)?;
    let (target_left, target_right) = match (rule, target_expression) {
        (
            LeanArithmeticBuiltinCompilationKind::AddNonnegative
            | LeanArithmeticBuiltinCompilationKind::AddPositive
            | LeanArithmeticBuiltinCompilationKind::AddPositiveLeftStrict
            | LeanArithmeticBuiltinCompilationKind::AddPositiveRightStrict,
            Obj::Add(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LeanArithmeticBuiltinCompilationKind::MulNonnegative
            | LeanArithmeticBuiltinCompilationKind::MulPositive,
            Obj::Mul(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        (
            LeanArithmeticBuiltinCompilationKind::DivNonnegative
            | LeanArithmeticBuiltinCompilationKind::DivPositive,
            Obj::Div(operation),
        ) => (operation.left.as_ref(), operation.right.as_ref()),
        _ => {
            return Err(format!(
                "sign builtin rule {rule:?} changed its target operator"
            ));
        }
    };
    let (left_zero, left_operand) = positive_order_parts(&premises[0].fact, left_is_strict)?;
    let (right_zero, right_operand) = positive_order_parts(&premises[1].fact, right_is_strict)?;
    if target_zero.to_string() != "0"
        || left_zero.to_string() != "0"
        || right_zero.to_string() != "0"
    {
        return Err("sign builtin rule changed its zero endpoint".into());
    }
    if obj_equality_key(target_left) != obj_equality_key(left_operand)
        || obj_equality_key(target_right) != obj_equality_key(right_operand)
    {
        return Err("sign builtin rule premises do not match its ordered operands".into());
    }

    render_fact(fact, context)?;
    let left = transport_zero_ended_order_proof_to_rendered_numeric_operand(
        left_operand,
        left_is_strict,
        &premises[0].proof_expression,
        context,
    )?;
    let right = transport_zero_ended_order_proof_to_rendered_numeric_operand(
        right_operand,
        right_is_strict,
        &premises[1].proof_expression,
        context,
    )?;
    Ok(format!("Litex.Rules.{theorem} ({left}) ({right})"))
}

/// A source-domain sign premise is stated about the heterogeneous parameter,
/// while arithmetic target expressions use the exact numeric Complex
/// representative selected by that parameter's membership proof. Transport
/// only across the equality bridge installed by the active compiler frame.
pub(in super::super) fn transport_zero_ended_order_proof_to_rendered_numeric_operand(
    source_operand: &Obj,
    strict: bool,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    {
        if context
            .semantic_zero_ended_order_symbols
            .contains(&symbol_id)
        {
            let rendered_source = render_obj(source_operand, context)?;
            let rendered_target = render_numeric_obj(source_operand, context)?;
            if rendered_source == rendered_target {
                return Ok(source_proof.to_string());
            }
            let equality = context
                .numeric_representation_equalities
                .get(&symbol_id)
                .ok_or_else(|| {
                    format!(
                        "semantic sign proof for `{rendered_source}` has no visible exact numeric equality bridge"
                    )
                })?;
            let predicate = if strict {
                "Litex.Positive"
            } else {
                "Litex.Nonnegative"
            };
            return Ok(format!(
                "({predicate}.congr ({equality})).mp ({source_proof})"
            ));
        }
        if let Some(real) = context.numeric_real_values.get(&symbol_id) {
            return Ok(format!(
                "Litex.Rules.{} {real} ({source_proof})",
                if strict {
                    "realCastPositive"
                } else {
                    "realCastNonnegative"
                }
            ));
        }
    }
    let rendered_source = render_obj(source_operand, context)?;
    let rendered_target = render_numeric_obj(source_operand, context)?;
    if rendered_source == rendered_target {
        return Ok(source_proof.to_string());
    }
    let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    else {
        return Err(format!(
            "sign proof changed `{rendered_source}` to unrelated numeric target `{rendered_target}`"
        ));
    };
    let equality = context
        .numeric_representation_equalities
        .get(&symbol_id)
        .ok_or_else(|| {
            format!(
                "sign proof for `{rendered_source}` has no visible exact numeric equality bridge"
            )
        })?;
    let predicate = if strict {
        "Litex.Positive"
    } else {
        "Litex.Nonnegative"
    };
    Ok(format!(
        "({predicate}.congr ({equality})).mp ({source_proof})"
    ))
}

/// Transport the exact sign proposition retained by one typed infer premise
/// from its source object to the numeric representative selected in the
/// current compiler frame. Both zero orientations are supported because
/// Litex stores positive/nonnegative and negative/nonpositive facts as
/// distinct source comparisons.
pub(in super::super) fn transport_zero_ended_order_fact_proof_to_current_numeric_representation(
    source_fact: &Fact,
    source_proof: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (source_left, source_right, strict) = order_relation_parts(source_fact)?;
    let (source_operand, predicate) = if is_literal_zero(source_left) {
        (
            source_right,
            if strict {
                "Litex.Positive"
            } else {
                "Litex.Nonnegative"
            },
        )
    } else if is_literal_zero(source_right) {
        (
            source_left,
            if strict {
                "Litex.Negative"
            } else {
                "Litex.Nonpositive"
            },
        )
    } else {
        return Err(format!(
            "typed zero-order inference retained a nonzero-ended premise `{source_fact}`"
        ));
    };

    if let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    {
        if context
            .semantic_zero_ended_order_symbols
            .contains(&symbol_id)
        {
            let rendered_source = render_obj(source_operand, context)?;
            let rendered_target = render_numeric_obj(source_operand, context)?;
            if rendered_source == rendered_target {
                return Ok(source_proof.to_string());
            }
            let equality = context
                .numeric_representation_equalities
                .get(&symbol_id)
                .ok_or_else(|| {
                    format!(
                        "semantic zero-order proof for `{rendered_source}` has no visible exact numeric equality bridge"
                    )
                })?;
            return Ok(format!(
                "({predicate}.congr ({equality})).mp ({source_proof})"
            ));
        }
        if let Some(real) = context.numeric_real_values.get(&symbol_id) {
            let theorem = match (is_literal_zero(source_left), strict) {
                (true, true) => "realCastPositive",
                (true, false) => "realCastNonnegative",
                (false, true) => "realCastNegative",
                (false, false) => "realCastNonpositive",
            };
            return Ok(format!("Litex.Rules.{theorem} {real} ({source_proof})"));
        }
    }

    let rendered_source = render_obj(source_operand, context)?;
    let rendered_target = render_numeric_obj(source_operand, context)?;
    if rendered_source == rendered_target {
        return Ok(source_proof.to_string());
    }
    let LeanTargetObjectRepresentation::Symbol { symbol_id, .. } =
        LeanTargetObjectRepresentation::lower(source_operand)?
    else {
        return Err(format!(
            "zero-order proof changed `{rendered_source}` to unrelated numeric target `{rendered_target}`"
        ));
    };
    let equality = context
        .numeric_representation_equalities
        .get(&symbol_id)
        .ok_or_else(|| {
            format!(
                "zero-order proof for `{rendered_source}` has no visible exact numeric equality bridge"
            )
        })?;
    Ok(format!(
        "({predicate}.congr ({equality})).mp ({source_proof})"
    ))
}

pub(in super::super) fn render_real_operand_membership(
    object: &Obj,
    fallback: &str,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> String {
    // Prefer the exact native-real representation selected by verifier-owned
    // carrier evidence.  This is not limited to bare symbols: function
    // applications and compound real expressions also have exact target
    // representations, and their membership proof must mention the same
    // complex cast that appears in generated arithmetic.
    if let Ok(target) = LeanTargetObjectRepresentation::lower(object) {
        if matches!(
            target,
            LeanTargetObjectRepresentation::Symbol { .. }
                | LeanTargetObjectRepresentation::FunctionApplication(_)
        ) {
            if let Ok(real) = render_real_target_object_representation(&target, context) {
                return format!(
                "(by simpa [Litex.abs, ← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] using (Litex.Rules.complexRealInR ({real})))"
            );
            }
        }
    }
    fallback.to_string()
}
