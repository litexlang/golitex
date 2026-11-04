//! Replay matrix-scalar expansion and its recorded finite aggregate evaluation.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{
    AggregateEvaluationResult, FunctionApplicationEvaluationResult, MatrixScalarEvaluationResult,
};
use crate::execute::execute_fact_stmt::native_matrix::{matrix_call, matrix_identifier};
use crate::prelude::*;

pub(super) fn validate_scalar_sum(native: &Obj, expression: &Obj) -> Result<(), LeanCompileError> {
    let dimension = match native {
        Obj::MatrixOperator(MatrixOperator::Trace(p)) => &p.order,
        Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) => &p.dimension,
        _ => return Err(LeanCompileError::unsupported("Matrix/ScalarSumSubject")),
    };
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = expression else {
        return Err(LeanCompileError::unsupported("Matrix/ScalarSum"));
    };
    if !matches!(sum.set.as_ref(), Obj::SetFormer(SetFormer::ClosedRange(r))
        if closed_integer(&r.start) == Some(1) && r.end.ir() == dimension.ir())
    {
        return Err(LeanCompileError::unsupported("Matrix/ScalarSumIndices"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
        return Err(LeanCompileError::unsupported("Matrix/ScalarSumIterand"));
    };
    let groups = &f.body.set_bound_parameters.groups;
    if groups.len() != 1
        || groups[0].params.len() != 1
        || groups[0].param_type.ir() != sum.set.ir()
        || !f.body.dom_facts.is_empty()
        || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
    {
        return Err(LeanCompileError::unsupported("Matrix/ScalarSumSignature"));
    }
    let k = matrix_identifier(&groups[0].params[0]);
    let expected = match native {
        Obj::MatrixOperator(MatrixOperator::Trace(p)) => matrix_call(&p.matrix, vec![k.clone(), k]),
        Obj::MatrixOperator(MatrixOperator::InnerProduct(p)) => {
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: Box::new(Obj::ComplexOperator(ComplexOperator::Conjugate(
                    Conjugate {
                        arg: Box::new(matrix_call(&p.left, vec![k.clone()])),
                    },
                ))),
                right: Box::new(matrix_call(&p.right, vec![k])),
            }))
        }
        _ => unreachable!(),
    };
    if f.equal_to.ir() != expected.ir() {
        return Err(LeanCompileError::unsupported("Matrix/ScalarSumBody"));
    }
    Ok(())
}

impl LitexToLeanCompiler {
    pub(super) fn compile_eval_matrix_value(
        &self,
        object: &Obj,
        functions: &[FunctionApplicationEvaluationResult],
        remaining_functions: &mut usize,
        aggregates: &[AggregateEvaluationResult],
        remaining_aggregates: &mut usize,
        matrices: &[MatrixScalarEvaluationResult],
        remaining_matrices: &mut usize,
        position: &SourcePosition<'_>,
    ) -> Result<(EvalRational, String, Vec<FactId>), LeanCompileError> {
        let index = remaining_matrices
            .checked_sub(1)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/MatrixMissing"))?;
        let p = &matrices[index];
        if p.source.ir() != object.ir() {
            return Err(LeanCompileError::unsupported("Eval/MatrixOrder"));
        }
        ensure_object(object, &p.source_well_defined)?;
        let original = self.compile_wd(&p.source_well_defined, position)?;
        let formed = SourcePosition::new(
            Some(position),
            SourceOwner::WD(&p.source_well_defined),
            usize::MAX,
        );
        // The recorded empty determinant expands directly to one. There is
        // no child aggregate to consume; unrelated aggregate cursors stay put.
        if matches!(object, Obj::MatrixOperator(MatrixOperator::Determinant(d))
            if matches!(d.order.as_ref(), Obj::Literal(Literal::Number(_)))
                && closed_integer(&d.order) == Some(0))
        {
            if !matches!(&p.expression, Obj::Literal(Literal::Number(_)))
                || closed_integer(&p.expression) != Some(1)
            {
                return Err(LeanCompileError::unsupported(
                    "Eval/EmptyDeterminantOriginalExpansion",
                ));
            }
            *remaining_matrices = index;
            let (value, calculated, cites) = self.compile_eval_value(
                &p.expression,
                functions,
                remaining_functions,
                aggregates,
                remaining_aggregates,
                matrices,
                remaining_matrices,
                &formed,
            )?;
            if EvalRational::from_obj(&p.value).as_ref() != Some(&value) {
                return Err(LeanCompileError::unsupported("Eval/MatrixValue"));
            }
            return Ok((value, format!(
                "(by\n  let _matrix_scalar := {original}\n  exact (Litex.matrixDeterminantZero (Litex.denote _matrix_scalar.val.matrix)).trans {calculated})"
            ), cites));
        }
        let aggregate_index = remaining_aggregates
            .checked_sub(1)
            .ok_or_else(|| LeanCompileError::unsupported("Eval/MatrixAggregateMissing"))?;
        let bridge = self.compile_matrix_scalar_definition(
            object,
            &p.expression,
            &aggregates[aggregate_index],
            &formed,
        )?;
        *remaining_matrices = index;
        let (value, calculated, cites) = self.compile_eval_value(
            &p.expression,
            functions,
            remaining_functions,
            aggregates,
            remaining_aggregates,
            matrices,
            remaining_matrices,
            &formed,
        )?;
        if EvalRational::from_obj(&p.value).as_ref() != Some(&value) {
            return Err(LeanCompileError::unsupported("Eval/MatrixValue"));
        }
        Ok((
            value,
            format!(
                "(by\n  let _matrix_scalar := {original}\n  exact {bridge}.trans {calculated})"
            ),
            cites,
        ))
    }

    /// Nonempty sums retain their checked iterand through an original term call.
    /// Empty sums need only their recorded empty enumeration.
    pub(super) fn compile_matrix_scalar_definition(
        &self,
        object: &Obj,
        expression: &Obj,
        aggregate: &AggregateEvaluationResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (sum, scalar) = match object {
            Obj::MatrixOperator(MatrixOperator::Trace(_) | MatrixOperator::InnerProduct(_)) => {
                validate_scalar_sum(object, expression)?;
                (expression, "M.number")
            }
            Obj::MatrixOperator(
                MatrixOperator::FrobeniusNorm(_) | MatrixOperator::EuclideanNorm(_),
            ) => {
                let Obj::ExpLogOperator(ExpLogOperator::Sqrt(root)) = expression else {
                    return Err(LeanCompileError::unsupported("Eval/MatrixNormRoot"));
                };
                super::compile_matrix_norm::validate_norm_sum(object, &root.arg)?;
                (
                    root.arg.as_ref(),
                    "(fun z : ℂ => Litex.sqrtValue (M.number z))",
                )
            }
            _ => return Err(LeanCompileError::unsupported("Eval/MatrixScalarFamily")),
        };
        let AggregateEvaluationResult::SumOfFiniteSet(aggregate) = aggregate else {
            return Err(LeanCompileError::unsupported("Eval/MatrixAggregateFamily"));
        };
        if aggregate.source.ir() != sum.ir() {
            return Err(LeanCompileError::unsupported("Eval/MatrixAggregateSubject"));
        }
        let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = sum else {
            return Err(LeanCompileError::unsupported("Eval/MatrixAggregateSubject"));
        };
        if let Some(term) = aggregate.terms.first() {
            ensure_object(&term.application, &term.application_well_defined)?;
            let Obj::FnObj(call) = &term.application else {
                return Err(LeanCompileError::unsupported("Eval/MatrixIterandCall"));
            };
            let FnObjHead::AnonymousFnLiteral(function) = call.head.as_ref() else {
                return Err(LeanCompileError::unsupported("Eval/MatrixIterandCall"));
            };
            let head = Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()));
            if head.ir() != sum.func.ir()
                || call.body.len() != 1
                || call.body[0].len() != 1
                || call.body[0][0].ir() != term.argument.ir()
            {
                return Err(LeanCompileError::unsupported("Eval/MatrixIterandCall"));
            }
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::WD(&term.application_well_defined),
                usize::MAX,
            );
            self.compile_wd(&term.application_well_defined, position)?;
            let function = self.compile_object_reference(&sum.func, &formed)?;
            let original = self.compile_object_reference(object, position)?;
            let source_value = self.compile_normalization_value(object, position)?;
            let expanded_value = self.compile_normalization_value(expression, &formed)?;
            let formula = match object {
                Obj::MatrixOperator(MatrixOperator::Trace(_)) => "matrixTraceFormula",
                Obj::MatrixOperator(MatrixOperator::InnerProduct(_)) => "finiteInnerProductFormula",
                Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_)) => "euclideanNormFormula",
                Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(_)) => "frobeniusNormFormula",
                _ => unreachable!(),
            };
            return Ok(format!("(show {source_value} = {expanded_value} from by\n  let _matrix_scalar := {original}\n  let _iterand := {function}\n  exact Litex.{formula} _matrix_scalar _iterand (by rfl) (by rfl))"));
        }
        let (elements, members) =
            self.compile_numeric_enumeration(&sum.set, &aggregate.enumeration, position)?;
        if !elements.is_empty() {
            return Err(LeanCompileError::unsupported("Eval/MatrixEmptyEnumeration"));
        }
        let source = self.compile_normalization_value(object, position)?;
        let expression = self.compile_normalization_value(expression, position)?;
        let set = self.compile_normalization_value(&sum.set, position)?;
        Ok(format!("(show {source} = {expression} from by\n  have _empty : ∀ x, ¬ M.mem x {set} := by\n    intro x hx\n    have impossible := ({members} x).mp hx\n    cases impossible\n  apply congrArg {scalar}\n  apply Litex.finiteAggregateValue_congr\n  intro x hx\n  exact False.elim (_empty x hx))"))
    }
}
