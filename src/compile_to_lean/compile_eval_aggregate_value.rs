use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, AggregateTermExpansion, FunctionApplicationEvaluationResult,
    MatrixScalarEvaluationResult,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_eval_aggregate_value(
        &self,
        object: &Obj,
        functions: &[FunctionApplicationEvaluationResult],
        remaining_functions: &mut usize,
        evaluations: &[AggregateEvaluationResult],
        remaining: &mut usize,
        matrices: &[MatrixScalarEvaluationResult],
        remaining_matrices: &mut usize,
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
            AggregateEvaluationResult::Reduce(p) => &p.source,
            AggregateEvaluationResult::FiniteSetReduce(p) => &p.source,
        };
        if object.ir() != source.ir() {
            return Err(LeanCompileError::unsupported("Eval/AggregateOrder"));
        }
        *remaining = index;
        let terms = match evidence {
            AggregateEvaluationResult::Sum(p) => p.terms.as_slice(),
            AggregateEvaluationResult::Product(p) => p.terms.as_slice(),
            AggregateEvaluationResult::SumOfFiniteSet(p) => p.terms.as_slice(),
            AggregateEvaluationResult::ProductOfFiniteSet(p) => p.terms.as_slice(),
            _ => &[],
        };
        // The evaluator records completed child calls and aggregates before
        // their parent. Consume the original term bodies in reverse order.
        let mut term_values = Vec::with_capacity(terms.len());
        let mut term_citations = Vec::with_capacity(terms.len());
        for term in terms.iter().rev() {
            let AggregateTermExpansion::Function(expansion) = &term.expansion else {
                return Err(LeanCompileError::unsupported(
                    "AggregateCalculation/Algorithm",
                ));
            };
            if term.nested_aggregate_evidence.end != *remaining
                || term.nested_aggregate_evidence.start > *remaining
            {
                return Err(LeanCompileError::unsupported("Eval/AggregateTermOrder"));
            }
            ensure_object(&term.application, &term.application_well_defined)?;
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::WD(&term.application_well_defined),
                usize::MAX,
            );
            let (value, proof, cites) = self.compile_eval_value(
                &expansion.expanded_body,
                functions,
                remaining_functions,
                evaluations,
                remaining,
                matrices,
                remaining_matrices,
                &formed,
            )?;
            if *remaining != term.nested_aggregate_evidence.start
                || EvalRational::from_obj(&term.value).as_ref() != Some(&value)
            {
                return Err(LeanCompileError::unsupported("Eval/AggregateTermValue"));
            }
            term_values.push(proof);
            term_citations.push(cites);
        }
        term_values.reverse();
        term_citations.reverse();
        let (value, proof) = match evidence {
            AggregateEvaluationResult::Sum(_) | AggregateEvaluationResult::Product(_) => {
                self.compile_range_aggregate_value(evidence, &term_values, position)?
            }
            AggregateEvaluationResult::Reduce(p) => self.compile_range_fold_value(p, position)?,
            AggregateEvaluationResult::FiniteSetReduce(p) => {
                self.compile_finite_fold_value(p, position)?
            }
            _ => self.compile_finite_aggregate_value(evidence, &term_values, position)?,
        };
        let raw = self.compile_normalization_value(object, position)?;
        let number = exact_rational_literal(&value, "ℂ")?;
        Ok((
            value,
            format!("(show {raw} = M.number {number} from {proof})"),
            term_citations.into_iter().flatten().collect(),
        ))
    }
}
