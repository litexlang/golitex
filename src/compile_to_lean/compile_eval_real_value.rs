use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FunctionApplicationEvaluationResult,
};
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;

impl LitexToLeanCompiler {
    /// Replay exact real operations after their original ordered child evaluations.
    /// Native values are observations; the source constructors retain their WD.
    pub(super) fn compile_eval_real_value(
        &self,
        object: &Obj,
        evaluations: &[FunctionApplicationEvaluationResult],
        remaining: &mut usize,
        aggregates: &[AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let (operation, children) = arithmetic_constructor_pairs(object, object)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/RealOperation"))?;
        let mut checked = Vec::new();
        for (child, _) in children.iter().rev() {
            checked.push(self.compile_eval_value(
                child,
                evaluations,
                remaining,
                aggregates,
                remaining_aggregates,
                position,
            )?);
        }
        checked.reverse();
        let arguments = checked
            .iter()
            .map(|(value, _, _)| {
                ClosedNumericExpr::try_from_obj(&value.to_obj())
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/RealArgument"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let unary = || Box::new(arguments[0].clone());
        let binary = || {
            (
                Box::new(arguments[0].clone()),
                Box::new(arguments[1].clone()),
            )
        };
        let (residual, law) = match operation {
            "absValue" => (ClosedNumericExpr::Abs(unary()), "absValue_number"),
            "signValue" => (ClosedNumericExpr::Sign(unary()), "signValue_number"),
            "floorValue" => (
                ClosedNumericExpr::Floor(unary()),
                "roundingValue_number false",
            ),
            "ceilValue" => (
                ClosedNumericExpr::Ceil(unary()),
                "roundingValue_number true",
            ),
            "minValue" => {
                let (a, b) = binary();
                (ClosedNumericExpr::Min(a, b), "minMaxValue_number false")
            }
            "maxValue" => {
                let (a, b) = binary();
                (ClosedNumericExpr::Max(a, b), "minMaxValue_number true")
            }
            _ => return Err(LeanCompileError::unsupported("Eval/RealOperation")),
        };
        let value = EvalRational::from_obj(&residual.to_obj())
            .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactRealValue"))?;
        let output = exact_rational_literal(&value, "ℂ")?;
        let native = checked
            .iter()
            .map(|(v, _, _)| exact_rational_literal(v, "ℝ"))
            .collect::<Result<Vec<_>, _>>()?
            .join(" ");
        let op = arithmetic_operation_term(operation);
        let congruence = match checked.as_slice() {
            [(_, p, _)] => format!("(congrArg {op} {p})"),
            [(_, p, _), (_, q, _)] => format!("(congrArg₂ {op} {p} {q})"),
            _ => return Err(LeanCompileError::unsupported("Eval/RealArity")),
        };
        let raw = self.compile_normalization_value(object, position)?;
        let proof = format!("(show {raw} = M.number {output} from {congruence}.trans (by\n  have _numeric := Litex.{law} (M := M) {native}\n  norm_num [Real.sign] at _numeric\n  simpa only [neg_div] using _numeric))");
        let cites = checked.into_iter().flat_map(|(_, _, ids)| ids).collect();
        Ok((value, proof, cites))
    }
}
