//! Replay the original small-order determinant definition and its residual.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{mul, sub};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_number, MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_determinant_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixScalarDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let residual = match proof.equality.as_ref() {
            MatrixDefinitionResidualProof::Verified(residual) => Some(residual.as_ref()),
            MatrixDefinitionResidualProof::ExactEvaluation(_) => None,
            _ => return Err(LeanCompileError::unsupported("Matrix/DeterminantResidual")),
        };
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::MatrixOperator(MatrixOperator::Determinant(m)) = native else {
                continue;
            };
            if let Some(residual) = residual {
                let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(residual)?
                else {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/DeterminantResidualSubject",
                    ));
                };
                if equal.left.ir() != proof.expression.ir() {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/DeterminantResidualEndpoint",
                    ));
                }
                if equal.right.ir() != other.ir() {
                    continue;
                }
            }
            if !matches!(m.order.as_ref(), Obj::Literal(Literal::Number(_))) {
                return Err(LeanCompileError::unsupported(
                    "Matrix/DeterminantLiteralOrder",
                ));
            }
            let entry = |i, j| matrix_call(&m.matrix, vec![matrix_number(i), matrix_number(j)]);
            let (name, expression, domain, normalize) = match closed_integer(&m.order) {
                Some(0) => ("matrixDeterminantZero", matrix_number(1), "", ""),
                Some(1) => (
                    "matrixDeterminantOne",
                    entry(1, 1),
                    " _det.wd.2",
                    "\n    simp only [Litex.matrixEntryValue, Nat.cast_one] at _raw",
                ),
                Some(2) => (
                    "matrixDeterminantTwo",
                    sub(mul(entry(1, 1), entry(2, 2)), mul(entry(1, 2), entry(2, 1))),
                    " _det.wd.2",
                    "\n    simp only [Litex.matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at _raw",
                ),
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/DeterminantExpansionOrder",
                    ));
                }
            };
            if proof.expression.ir() != expression.ir() {
                return Err(LeanCompileError::unsupported("Matrix/DeterminantExpansion"));
            }
            let root = self.compile_object_reference(native, position)?;
            let orientation = if reversed { ".symm" } else { "" };
            if let MatrixDefinitionResidualProof::ExactEvaluation(evaluation) =
                proof.equality.as_ref()
            {
                let (raw, checked) = self.compile_matrix_exact_scalar(
                    &proof.expression,
                    other,
                    evaluation,
                    position,
                )?;
                return Ok(format!(
                    "(by\n  let _det := {root}\n  have _definition : Litex.denote _det = {raw} := by\n    have _raw := Litex.{name} (Litex.denote _det.val.matrix){domain}{normalize}\n    exact _raw\n  exact (_definition.trans {checked}){orientation}\n)"
                ));
            }
            let residual = residual.expect("verified determinant residual");
            let checked = self.compile_verify(residual, position)?.1;
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(residual), usize::MAX);
            let expanded = self.compile_object_reference(&proof.expression, &formed)?;
            let orientation = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(by\n  let _det := {root}\n  let _expanded := {expanded}\n  have _definition : Litex.Same _det _expanded := by\n    have _raw := Litex.{name} (Litex.denote _det.val.matrix){domain}{normalize}\n    exact _raw\n  exact (_definition.trans {checked}){orientation}\n)"
            ));
        }
        Err(LeanCompileError::unsupported(
            "Matrix/DeterminantDefinitionSubject",
        ))
    }
}
