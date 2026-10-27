//! Replay matrix trace WD, scalar membership and its original diagonal sum.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
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
            let Obj::MatrixOperator(MatrixOperator::Trace(m)) = native else {
                continue;
            };
            if equal.right.ir() != other.ir() {
                continue;
            }
            let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &proof.expression
            else {
                return Err(LeanCompileError::unsupported("Matrix/TraceSum"));
            };
            if !matches!(sum.set.as_ref(),Obj::SetFormer(SetFormer::ClosedRange(r)) if closed_integer(&r.start)==Some(1) && r.end.ir()==m.order.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/TraceIndices"));
            }
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
                return Err(LeanCompileError::unsupported("Matrix/TraceIterand"));
            };
            let groups = &f.body.set_bound_parameters.groups;
            if groups.len() != 1
                || groups[0].params.len() != 1
                || groups[0].param_type.ir() != sum.set.ir()
                || !f.body.dom_facts.is_empty()
                || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/TraceIterandSignature",
                ));
            }
            let k = matrix_identifier(&groups[0].params[0]);
            if f.equal_to.ir() != matrix_call(&m.matrix, vec![k.clone(), k]).ir() {
                return Err(LeanCompileError::unsupported("Matrix/TraceIterandBody"));
            }
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
