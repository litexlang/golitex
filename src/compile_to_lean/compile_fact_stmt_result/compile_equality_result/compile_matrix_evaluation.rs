//! Exact identity-matrix entries from the recorded scalar-evaluation result.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixComponentDefinitionProof, MatrixComponentReductionEvidence, MatrixExactEvaluationProof,
};
use crate::prelude::*;
use crate::execute::execute_eval_stmt::aggregate_evaluation_result::{FunctionApplicationEvaluationResult, FunctionApplicationExpansionProof};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_object_definition::by_fn_application::by_parent_checked_beta::ParentCheckedBetaFunctionBody;

impl LitexToLeanCompiler {
    pub(super) fn compile_identity_matrix_evaluation(
        &self,
        fact: &EqualFact,
        component: &MatrixComponentDefinitionProof,
        evaluation: &MatrixExactEvaluationProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if !matches!(
            component.callable.operator,
            MatrixOperator::IdentityMatrix(_)
        ) || !matches!(
            component.reduction.evidence,
            MatrixComponentReductionEvidence::Unchanged
        ) || component.reduction.value.ir() != component.body.ir()
            || !evaluation.cited_equal_fact_ids.is_empty()
            || !evaluation.matrix_scalar_evaluations.is_empty()
            || !evaluation.aggregate_evaluations.is_empty()
            || !evaluation.function_evaluations.is_empty()
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/ExactEvaluationStages",
            ));
        }
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::FnObj(call) = native else { continue };
            if call.body.len() != 1 || call.body[0].len() != 2 {
                continue;
            }
            let output = self.compile_numeric_observation(other, position)?;
            let original = self.compile_object_reference(native, position)?;
            let (value, step) = position
                .with_visible_wd(native, &mut |wd, producer| {
                    self.compile_matrix_component_step(
                        native,
                        &original,
                        &component.callable,
                        &component.body,
                        wd,
                        producer,
                    )
                })?
                .ok_or_else(|| LeanCompileError::unsupported("Matrix/ExactEvaluationProducer"))?;
            let (evaluated, result) = self.compile_identity_entry_value(call, &value, position)?;
            if EvalRational::from_obj(&evaluation.left_value).as_ref() != Some(&result)
                || EvalRational::from_obj(&evaluation.right_value).as_ref() != Some(&result)
                || output.3.as_ref() != Some(&result)
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/ExactEvaluationResult",
                ));
            }
            let target = exact_rational_literal(&result, "ℂ")?;
            let other_denote = format!(
                "(({}).trans (congrArg M.number (by norm_num : {} = {target})))",
                output.1, output.0
            );
            let proof = format!("(({step}).trans (({evaluated}).trans {other_denote}.symm))");
            return Ok(if reversed {
                format!("({proof}).symm")
            } else {
                proof
            });
        }
        Err(LeanCompileError::unsupported(
            "Matrix/ExactEvaluationSubject",
        ))
    }
    fn compile_identity_entry_value(
        &self,
        call: &FnObj,
        value: &str,
        position: &SourcePosition<'_>,
    ) -> Result<(String, EvalRational), LeanCompileError> {
        if call.body.len() != 1 || call.body[0].len() != 2 {
            return Err(LeanCompileError::unsupported("Matrix/ExactEvaluationArity"));
        }
        let row = self.compile_numeric_observation(&call.body[0][0], position)?;
        let col = self.compile_numeric_observation(&call.body[0][1], position)?;
        let (Some(row_value), Some(col_value)) = (&row.3, &col.3) else {
            return Err(LeanCompileError::unsupported(
                "Matrix/ExactEvaluationIndices",
            ));
        };
        let same = row_value == col_value;
        let result = EvalRational::new(if same { 1 } else { 0 }, 1).unwrap();
        let row_number = exact_rational_literal(row_value, "ℂ")?;
        let col_number = exact_rational_literal(col_value, "ℂ")?;
        let target = exact_rational_literal(&result, "ℂ")?;
        let row_object = self.compile_object_reference(&call.body[0][0], position)?;
        let col_object = self.compile_object_reference(&call.body[0][1], position)?;
        let law = if same {
            format!("Litex.matrixIdentityEntrySelf (M.number {row_number})")
        } else {
            format!(
                "Litex.matrixIdentityEntryDifferent (M.number {row_number}) (M.number {col_number}) (fun h => (by norm_num : {row_number} ≠ {col_number}) (M.number_injective h))"
            )
        };
        let evaluated = format!(
            "(show {value} = M.number {target} from by\n  have hi : Litex.denote {row_object} = M.number {row_number} := ({}).trans (congrArg M.number (by norm_num))\n  have hj : Litex.denote {col_object} = M.number {col_number} := ({}).trans (congrArg M.number (by norm_num))\n  exact (congrArg₂ (Litex.matrixIdentityEntry (M := M)) hi hj).trans ({law}))",
            row.1, col.1
        );

        Ok((evaluated, result))
    }

    /// Consume chronological function evaluations while traversing the original
    /// scalar expression. The iterator is local to this one result replay.
    fn compile_matrix_evaluated_expression(
        &self,
        expression: &Obj,
        evaluations: &mut std::iter::Enumerate<
            std::slice::Iter<'_, FunctionApplicationEvaluationResult>,
        >,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String, EvalRational), LeanCompileError> {
        if let Obj::Literal(Literal::Number(number)) = expression {
            let value = EvalRational::from_obj(expression)
                .ok_or_else(|| LeanCompileError::unsupported("Matrix/ExactScalarLiteral"))?;
            let input = number_literal(number, "ℂ")?;
            let target = exact_rational_literal(&value, "ℂ")?;
            return Ok((
                format!("(M.number {input})"),
                format!("(congrArg M.number (by norm_num : {input} = {target}))"),
                value,
            ));
        }
        if let Obj::FnObj(call) = expression {
            let (index, evidence) = evaluations
                .next()
                .ok_or_else(|| LeanCompileError::unsupported("Matrix/ExactFunctionMissing"))?;
            if evidence.application.ir() != expression.ir() {
                return Err(LeanCompileError::unsupported("Matrix/ExactFunctionOrder"));
            }
            ensure_object(expression, &evidence.application_well_defined)?;
            let FunctionApplicationExpansionProof::CheckedBeta(beta) = &evidence.expansion else {
                return Err(LeanCompileError::unsupported(
                    "Matrix/ExactFunctionExpansion",
                ));
            };
            if evidence.rewritten_body.ir() != beta.expanded_body.ir()
                || !evidence.cited_equal_fact_ids.is_empty()
                || evidence.nested_function_evidence != (index..index)
            {
                return Err(LeanCompileError::unsupported("Matrix/ExactFunctionStages"));
            }
            let ParentCheckedBetaFunctionBody::NativeMatrix(callable) = &beta.function_body else {
                return Err(LeanCompileError::unsupported("Matrix/ExactFunctionSource"));
            };
            let object = self.compile_wd(&evidence.application_well_defined, position)?;
            let (raw, step) = self.compile_matrix_component_step(
                expression,
                &object,
                callable,
                &beta.expanded_body,
                &evidence.application_well_defined,
                position,
            )?;
            let formed = SourcePosition::new(
                Some(position),
                SourceOwner::WD(&evidence.application_well_defined),
                usize::MAX,
            );
            let (evaluated, result) = match &callable.operator {
                MatrixOperator::IdentityMatrix(_) => {
                    self.compile_identity_entry_value(call, &raw, &formed)?
                }
                MatrixOperator::ZeroMatrix(_) => (
                    "(Eq.refl (M.number (0 : ℂ)))".into(),
                    EvalRational::new(0, 1).unwrap(),
                ),
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/ExactFunctionOperator",
                    ));
                }
            };
            if EvalRational::from_obj(&evidence.value).as_ref() != Some(&result) {
                return Err(LeanCompileError::unsupported("Matrix/ExactFunctionValue"));
            }
            return Ok((
                format!("(Litex.denote {object})"),
                format!("(({step}).trans {evaluated})"),
                result,
            ));
        }
        let (left, right, operation) = match expression {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(p)) => (&p.left, &p.right, "add"),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(p)) => (&p.left, &p.right, "sub"),
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(p)) => (&p.left, &p.right, "mul"),
            Obj::ArithmeticOperator(ArithmeticOperator::Div(p)) => (&p.left, &p.right, "div"),
            _ => {
                return Err(LeanCompileError::unsupported(
                    "Matrix/ExactScalarExpression",
                ));
            }
        };
        let (a, ha, x) = self.compile_matrix_evaluated_expression(left, evaluations, position)?;
        let (b, hb, y) = self.compile_matrix_evaluated_expression(right, evaluations, position)?;
        let value = match operation {
            "add" => x.add(&y),
            "sub" => x.sub(&y),
            "mul" => x.mul(&y),
            "div" => x.div(&y),
            _ => unreachable!(),
        }
        .ok_or_else(|| LeanCompileError::unsupported("Matrix/ExactScalarArithmetic"))?;
        let x = exact_rational_literal(&x, "ℂ")?;
        let y = exact_rational_literal(&y, "ℂ")?;
        let target = exact_rational_literal(&value, "ℂ")?;
        let symbol = match operation {
            "add" => "+",
            "sub" => "-",
            "mul" => "*",
            "div" => "/",
            _ => unreachable!(),
        };
        let guard = if operation == "div" {
            " (by norm_num)"
        } else {
            ""
        };
        let proof = format!(
            "((congrArg₂ M.{operation}Value {ha} {hb}).trans ((M.{operation}_numbers {x} {y}{guard}).trans (congrArg M.number (by norm_num : {x} {symbol} {y} = {target}))))"
        );
        Ok((format!("(M.{operation}Value {a} {b})"), proof, value))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_exact_scalar(
        &self,
        expression: &Obj,
        other: &Obj,
        evaluation: &MatrixExactEvaluationProof,
        position: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        if !evaluation.cited_equal_fact_ids.is_empty()
            || !evaluation.matrix_scalar_evaluations.is_empty()
            || !evaluation.aggregate_evaluations.is_empty()
        {
            return Err(LeanCompileError::unsupported("Matrix/ExactScalarStages"));
        }
        let mut evaluations = evaluation.function_evaluations.iter().enumerate();
        let (raw, left, x) =
            self.compile_matrix_evaluated_expression(expression, &mut evaluations, position)?;
        let (_, right, y) =
            self.compile_matrix_evaluated_expression(other, &mut evaluations, position)?;
        if evaluations.next().is_some()
            || x != y
            || EvalRational::from_obj(&evaluation.left_value).as_ref() != Some(&x)
            || EvalRational::from_obj(&evaluation.right_value).as_ref() != Some(&y)
        {
            return Err(LeanCompileError::unsupported("Matrix/ExactScalarResult"));
        }
        let output = self.compile_object_reference(other, position)?;
        let target = exact_rational_literal(&y, "ℂ")?;
        Ok((
            raw,
            format!(
                "(({left}).trans (show Litex.denote {output} = M.number {target} from {right}).symm)"
            ),
        ))
    }
}
