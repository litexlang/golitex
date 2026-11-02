//! Replay matrix trace WD, scalar membership and its original diagonal sum.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_trace_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixScalarDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let MatrixDefinitionResidualProof::Verified(residual) = proof.equality.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/TraceResidual"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported("Matrix/TraceResidualSubject"));
        };
        if equal.left.ir() != proof.expression.ir() {
            return Err(LeanCompileError::unsupported(
                "Matrix/TraceResidualEndpoint",
            ));
        }
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::MatrixOperator(MatrixOperator::Trace(_)) = native else {
                continue;
            };
            if equal.right.ir() != other.ir() {
                continue;
            }
            super::compile_eval_matrix_value::validate_scalar_sum(native, &proof.expression)?;
            let root = self.compile_object_reference(native, position)?;
            let checked = self.compile_verify(residual, position)?.1;
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(residual), usize::MAX);
            let expanded = self.compile_object_reference(&proof.expression, &formed)?;
            let bridge = format!(
                "(show Litex.Same {root} {expanded} from Litex.matrixTraceFormula {root} ({expanded}).val.function (by rfl) (by rfl))"
            );
            let result = format!("({bridge}.trans {checked})");
            return Ok(if reversed {
                format!("({result}).symm")
            } else {
                result
            });
        }
        Err(LeanCompileError::unsupported(
            "Matrix/TraceDefinitionSubject",
        ))
    }
}
