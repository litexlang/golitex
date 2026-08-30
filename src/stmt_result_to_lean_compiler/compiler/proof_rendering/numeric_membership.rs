//! Closed numeric membership rendering.

use super::super::*;

pub(in super::super) fn render_closed_numeric_membership_from_result(
    proposition: &Fact,
    evidence_target_set: StandardSet,
    evaluation: &SuccessEvaluateObjResult,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (element, set) = membership_parts(proposition)?;
    let Obj::StandardSet(target_set) = set else {
        return Err("closed-numeric-membership certificate targets a nonstandard set".into());
    };
    if *target_set != evidence_target_set
        || obj_equality_key(element) != obj_equality_key(&evaluation.expression)
    {
        return Err(
            "closed-numeric-membership certificate changed its expression or target set".into(),
        );
    }
    let reevaluated = evaluation
        .expression
        .evaluate_to_normalized_decimal_number()
        .ok_or_else(|| "closed-numeric-membership expression no longer evaluates".to_string())?;
    if reevaluated.normalized_value != evaluation.value.normalized_value {
        return Err("closed-numeric-membership normalized value was corrupted".into());
    }
    let source = render_obj(element, context)?;
    let normalized = &evaluation.value.normalized_value;
    match target_set {
        StandardSet::C => Ok(format!("Litex.Rules.complexInC {source}")),
        StandardSet::N
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit()) =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInN {source} {normalized} (by norm_num)"
            ))
        }
        StandardSet::NPos
            if normalized
                .chars()
                .all(|character| character.is_ascii_digit())
                && normalized.chars().any(|character| character != '0') =>
        {
            Ok(format!(
                "Litex.Rules.complexEqNatInNPos {source} {normalized} (by norm_num) (by norm_num)"
            ))
        }
        StandardSet::Z => Ok(format!(
            "Litex.Rules.complexEqIntInZ {source} {normalized} (by norm_num)"
        )),
        StandardSet::Q => Ok(format!(
            "Litex.Rules.complexEqRatInQ {source} {normalized} (by norm_num)"
        )),
        StandardSet::QPos => Ok(format!(
            "Litex.Rules.complexEqRatInQPos {source} ({normalized} : ℚ) (by norm_num) (by norm_num)"
        )),
        StandardSet::ZNeg => Ok(format!(
            "Litex.Rules.complexEqIntInZNeg {source} ({normalized} : ℤ) (by norm_num) (by norm_num)"
        )),
        StandardSet::QNeg => Ok(format!(
            "Litex.Rules.complexEqRatInQNeg {source} ({normalized} : ℚ) (by norm_num) (by norm_num)"
        )),
        StandardSet::R => render_closed_real_expression_membership(element, context),
        StandardSet::RPos => Ok(format!(
            "Litex.Rules.complexEqRealInRPos {source} ({normalized} : ℝ) (by norm_num) (by norm_num)"
        )),
        StandardSet::RNeg => Ok(format!(
            "Litex.Rules.complexEqRealInRNeg {source} ({normalized} : ℝ) (by norm_num) (by norm_num)"
        )),
        _ => Err(format!(
            "unsupported closed numeric membership in `{target_set}` with value `{normalized}`"
        )),
    }
}

pub(in super::super) fn render_closed_real_expression_membership(
    element: &Obj,
    context: &StmtResultToLeanCompilerEnvironmentStack,
) -> Result<String, String> {
    let (left, right, theorem) = match element {
        Obj::Add(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexAddInR",
        ),
        Obj::Sub(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexSubInR",
        ),
        Obj::Mul(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexMulInR",
        ),
        Obj::Div(operation) => (
            operation.left.as_ref(),
            operation.right.as_ref(),
            "complexDivInR",
        ),
        Obj::Number(number) => {
            if number.normalized_value.parse::<i128>().is_err() {
                return Err(
                    "closed real-expression membership requires integral numeral leaves".into(),
                );
            }
            return Ok(format!(
                "Litex.Rules.complexRealInR ({} : ℝ)",
                number.normalized_value
            ));
        }
        _ => {
            return Err(format!(
                "closed real-expression membership has unsupported operand `{element}`"
            ));
        }
    };
    render_obj(element, context)?;
    Ok(format!(
        "Litex.Rules.{theorem} ({}) ({})",
        render_closed_real_expression_membership(left, context)?,
        render_closed_real_expression_membership(right, context)?
    ))
}
