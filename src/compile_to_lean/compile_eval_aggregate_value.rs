use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::AggregateEvaluationResult;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_eval_aggregate_value(
        &self,
        object: &Obj,
        evaluations: &[AggregateEvaluationResult],
        remaining: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let index = remaining
            .checked_sub(1)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/AggregateMissing"))?;
        let evidence = &evaluations[index];
        let source = match evidence {
            AggregateEvaluationResult::Sum(p) => &p.source,
            AggregateEvaluationResult::Product(p) => &p.source,
            AggregateEvaluationResult::SumOfFiniteSet(p) => &p.source,
            AggregateEvaluationResult::ProductOfFiniteSet(p) => &p.source,
            _ => return Err(LeanCompileError::unsupported("Eval/AggregateFamily")),
        };
        if object.ir() != source.ir() {
            return Err(LeanCompileError::unsupported("Eval/AggregateOrder"));
        }
        let (value, proof) = match evidence {
            AggregateEvaluationResult::Sum(_) | AggregateEvaluationResult::Product(_) => {
                self.compile_range_aggregate_value(evidence, position)?
            }
            _ => self.compile_finite_aggregate_value(evidence, position)?,
        };
        *remaining = index;
        let raw = self.compile_normalization_value(object, position)?;
        let number = exact_rational_literal(&value, "ℂ")?;
        Ok((
            value,
            format!("(show {raw} = M.number {number} from {proof})"),
            vec![],
        ))
    }
}
