use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FunctionApplicationEvaluationResult,
};
use crate::prelude::*;
use crate::rational_expression::ClosedNumericExpr;

impl LitexToLeanCompiler {
    /// Replay the evaluator's exact rational logarithm and its child records.
    pub(super) fn compile_eval_log_value(
        &self,
        object: &Obj,
        evaluations: &[FunctionApplicationEvaluationResult],
        remaining: &mut usize,
        aggregates: &[AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let Obj::ExpLogOperator(ExpLogOperator::Log(log)) = object else {
            return Err(LeanCompileError::unsupported("Eval/LogObject"));
        };
        // Reverse traversal matches the evaluator's postorder call records.
        let (argument, argument_proof, argument_cites) = self.compile_eval_value(
            &log.arg,
            evaluations,
            remaining,
            aggregates,
            remaining_aggregates,
            position,
        )?;
        let (base, base_proof, mut cites) = self.compile_eval_value(
            &log.base,
            evaluations,
            remaining,
            aggregates,
            remaining_aggregates,
            position,
        )?;
        cites.extend(argument_cites);
        let residual = ClosedNumericExpr::Log {
            base: Box::new(
                ClosedNumericExpr::try_from_obj(&base.to_obj())
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/LogBase"))?,
            ),
            arg: Box::new(
                ClosedNumericExpr::try_from_obj(&argument.to_obj())
                    .ok_or_else(|| LeanCompileError::unsupported("Eval/LogArgument"))?,
            ),
        };
        let value = EvalRational::from_obj(&residual.to_obj())
            .ok_or_else(|| LeanCompileError::unsupported("Eval/ExactLogarithm"))?;
        let (p, q) = value.parts();
        let base_real = exact_rational_literal(&base, "ℝ")?;
        let arg_real = exact_rational_literal(&argument, "ℝ")?;
        let base_complex = exact_rational_literal(&base, "ℂ")?;
        let arg_complex = exact_rational_literal(&argument, "ℂ")?;
        let result_real = exact_rational_literal(&value, "ℝ")?;
        let result_complex = exact_rational_literal(&value, "ℂ")?;
        let raw = self.compile_normalization_value(object, position)?;
        let operation = arithmetic_operation_term("logValue");
        let proof = format!("(show {raw} = M.number {result_complex} from (congrArg₂ {operation} {base_proof} {argument_proof}).trans (by\n  have _base_cast : {base_complex} = (({base_real} : ℝ) : ℂ) := by norm_num\n  have _arg_cast : {arg_complex} = (({arg_real} : ℝ) : ℂ) := by norm_num\n  have _base_nonzero : ((Real.log {base_real} : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < {base_real}) (by norm_num : {base_real} ≠ 1))\n  have _value : Real.log {arg_real} / Real.log {base_real} = {result_real} := (Litex.rationalLogValue {base_real} {arg_real} ({p} : ℤ) ({q} : ℕ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).trans (by norm_num)\n  have _base := (congrArg (Litex.realUnaryValue (M := M) Real.log) (congrArg M.number _base_cast)).trans (Litex.realUnaryValue_number (M := M) Real.log {base_real})\n  have _arg := (congrArg (Litex.realUnaryValue (M := M) Real.log) (congrArg M.number _arg_cast)).trans (Litex.realUnaryValue_number (M := M) Real.log {arg_real})\n  exact (congrArg₂ M.divValue _arg _base).trans ((M.div_numbers _ _ _base_nonzero).trans (congrArg M.number (by rw [← Complex.ofReal_div, _value]; norm_num)))))");
        Ok((value, proof, cites))
    }
}
