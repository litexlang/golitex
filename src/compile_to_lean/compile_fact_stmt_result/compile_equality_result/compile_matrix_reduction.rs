//! Replay the producer's ordered native matrix component expansion.
use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixCallableProof, MatrixComponentReduction, MatrixComponentReductionEvidence,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_matrix_component_step(
        &self,
        subject: &Obj,
        call_object: &str,
        callable: &MatrixCallableProof,
        body: &Obj,
        wd: &ObjWellDefinedProof,
        producer: &SourcePosition<'_>,
    ) -> Result<(String, String), LeanCompileError> {
        Self::validate_matrix_callable(callable)?;
        ensure_object(subject, wd)?;
        let Obj::FnObj(call) = subject else {
            return Err(LeanCompileError::unsupported("Matrix/ComponentCall"));
        };
        let arity = if matches!(callable.operator, MatrixOperator::Apply(_)) {
            1
        } else {
            2
        };
        if call.body.len() != 1 || call.body[0].len() != arity {
            return Err(LeanCompileError::unsupported("Matrix/ComponentArity"));
        }
        let substitution = callable
            .function
            .body
            .set_bound_parameters
            .groups
            .iter()
            .flat_map(|g| &g.params)
            .zip(&call.body[0])
            .map(|(p, a)| (p.id, a.as_ref().clone()))
            .collect();
        if !instantiated_object_matches(&callable.function.equal_to, body, &substitution) {
            return Err(LeanCompileError::unsupported(
                "Matrix/ComponentSubstitution",
            ));
        }
        let DetailedObjWellDefinedProof::ByDef {
            proof: ObjWellDefinedProofByDef::FnObj(p),
            ..
        } = (wd).detailed_ref()
        else {
            return Err(LeanCompileError::unsupported("Matrix/ComponentCallWD"));
        };
        let scope = SourcePosition::new(Some(producer), SourceOwner::WD(wd), usize::MAX);
        let root = self.compile_matrix_callable_root(callable, &scope)?;
        let head = match call.head.as_ref() {
            FnObjHead::Identifier(i) => Obj::Identifier(i.clone()),
            FnObjHead::Object(o) => o.as_ref().clone(),
            _ => return Err(LeanCompileError::unsupported("Matrix/ComponentHead")),
        };
        let same = self.compile_equality_path(
            &head,
            &Obj::MatrixOperator(callable.operator.clone()),
            &callable.function_equal,
            &scope,
        )?;
        let (input, domain) = self.compile_fn_return_domain(
            call,
            p,
            &callable.function.body,
            &SourcePosition { before: 0, ..scope },
        )?;
        let transport = format!(
            "(congrArg (fun f => Litex.FunctionSemantics.callValue (M := M) f {input}) {same})"
        );
        match &callable.operator {
            MatrixOperator::Add(_) | MatrixOperator::Subtract(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let operation = if matches!(callable.operator, MatrixOperator::Add(_)) {
                    "add"
                } else {
                    "sub"
                };
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = format!(
                    "(M.{operation}Value (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.left) {pair}) (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.right) {pair}))"
                );
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixEntrywiseCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixEntrywiseBody .{operation} (Litex.denote ({root}).val.left) (Litex.denote ({root}).val.right) {pair} at h\n  dsimp only [Litex.matrixEntrywiseBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::Apply(_) => {
                let value = self.compile_function_raw_expression_bound(
                    body,
                    &scope,
                    &std::collections::HashMap::new(),
                )?;
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from {transport}.trans (Litex.matrixApplyCall {root} {input} {domain}))"
                );
                Ok((value, proof))
            }
            MatrixOperator::Inverse(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!("(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))");
                let value = format!("(M.divValue (Litex.matrixCofactorValue (Litex.denote ({root}).val.matrix) ({root}).val.order (Litex.denote {col}) (Litex.denote {row})) (Litex.matrixDeterminantValue (Litex.denote ({root}).val.matrix) ({root}).val.order))");
                let proof = format!("(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixInverseCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixInverseBody (Litex.denote ({root}).val.matrix) ({root}).val.order {pair} at h\n  unfold Litex.matrixInverseBody Litex.matrixAdjugateBody at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)");
                Ok((value, proof))
            }
            MatrixOperator::Adjugate(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!("(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))");
                let value = format!("(Litex.matrixCofactorValue (Litex.denote ({root}).val.matrix) ({root}).val.order (Litex.denote {col}) (Litex.denote {row}))");
                let proof = format!("(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixAdjugateCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixAdjugateBody (Litex.denote ({root}).val.matrix) ({root}).val.order {pair} at h\n  unfold Litex.matrixAdjugateBody at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)");
                Ok((value, proof))
            }
            MatrixOperator::Minor(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = self.compile_function_raw_expression_bound(
                    body,
                    &scope,
                    &std::collections::HashMap::new(),
                )?;
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixMinorCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixMinorBody (Litex.denote ({root}).val.matrix) (Litex.denote ({root}).val.order) (Litex.denote ({root}).val.row) (Litex.denote ({root}).val.col) {pair} at h\n  unfold Litex.matrixMinorBody Litex.matrixMinorShift at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::Multiply(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = self.compile_function_raw_expression_bound(
                    body,
                    &scope,
                    &std::collections::HashMap::new(),
                )?;
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixMultiplyCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixMultiplyBody (Litex.denote ({root}).val.left) (Litex.denote ({root}).val.right) ({root}).val.inner {pair} at h\n  unfold Litex.matrixMultiplyBody Litex.matrixMultiplyTerm at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::Scale(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = format!(
                    "(M.mulValue (Litex.denote ({root}).val.scalar) (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.matrix) {pair}))"
                );
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixScaleCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixScaleBody (Litex.denote ({root}).val.scalar) (Litex.denote ({root}).val.matrix) {pair} at h\n  dsimp only [Litex.matrixScaleBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::OuterProduct(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = format!(
                    "(M.mulValue (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.left) (Litex.denote {row})) (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.right) (Litex.denote {col})))"
                );
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixOuterCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixOuterBody (Litex.denote ({root}).val.left) (Litex.denote ({root}).val.right) {pair} at h\n  dsimp only [Litex.matrixOuterBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::Diagonal(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let pair = format!(
                    "(Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col}))"
                );
                let value = format!(
                    "(M.mulValue (Litex.matrixIdentityEntry (Litex.denote {row}) (Litex.denote {col})) (Litex.FunctionSemantics.callValue (Litex.denote ({root}).val.vector) (Litex.denote {row})))"
                );
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.matrixDiagonalCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixDiagonalBody (Litex.denote ({root}).val.vector) {pair} at h\n  dsimp only [Litex.matrixDiagonalBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::ZeroMatrix(_) => Ok((
                "(M.number 0)".into(),
                format!(
                    "(show Litex.denote {call_object} = M.number 0 from {transport}.trans (Litex.zeroMatrixCall {root} {input} {domain}))"
                ),
            )),
            MatrixOperator::IdentityMatrix(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let value = format!(
                    "(Litex.matrixIdentityEntry (Litex.denote {row}) (Litex.denote {col}))"
                );
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.identityMatrixCall {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.matrixIdentityBody (Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col})) at h\n  dsimp only [Litex.matrixIdentityBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            MatrixOperator::Transpose(_) | MatrixOperator::ConjugateTranspose(_) => {
                let row = self.compile_object_reference(&call.body[0][0], &scope)?;
                let col = self.compile_object_reference(&call.body[0][1], &scope)?;
                let value = format!(
                    "(Litex.FunctionSemantics.callValue (M := M) (Litex.denote ({root}).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote {col}) (Litex.denote {row})))"
                );
                let (name, body_name, value) = match &callable.operator {
                    MatrixOperator::ConjugateTranspose(_) => (
                        "conjugateTranspose",
                        "matrixConjugateTransposeBody",
                        format!("(Litex.complexUnaryValue (M := M) (fun z : ℂ => star z) {value})"),
                    ),
                    _ => ("transpose", "matrixTransposeBody", value),
                };
                let proof = format!(
                    "(show Litex.denote {call_object} = {value} from by\n  have h := {transport}.trans (Litex.{name}Call {root} {input} {domain})\n  change Litex.denote {call_object} = Litex.{body_name} (Litex.denote ({root}).val.matrix) (Litex.FiniteFunction.pack2 (Litex.denote {row}) (Litex.denote {col})) at h\n  dsimp only [Litex.matrixConjugateTransposeBody, Litex.matrixTransposeBody] at h\n  rw [Litex.FiniteFunction.unpack_pack2] at h\n  exact h)"
                );
                Ok((value, proof))
            }
            _ => Err(LeanCompileError::unsupported("Matrix/ComponentOperator")),
        }
    }

    pub(super) fn compile_matrix_component_reduction(
        &self,
        subject: &Obj,
        value: &str,
        proof: &MatrixComponentReduction,
        endpoint: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match &proof.evidence {
            MatrixComponentReductionEvidence::Unchanged => {
                if subject.ir() != proof.value.ir() {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/ComponentReductionIdentity",
                    ));
                }
                Ok(format!("(show {value} = {endpoint} from rfl)"))
            }
            MatrixComponentReductionEvidence::NativeApplication(p) => {
                ensure_object(subject, &p.application_well_defined)?;
                if p.continuation.value.ir() != proof.value.ir() {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/ComponentReductionEndpoint",
                    ));
                }
                let call = self.compile_wd(&p.application_well_defined, position)?;
                let scope = SourcePosition::new(
                    Some(position),
                    SourceOwner::WD(&p.application_well_defined),
                    usize::MAX,
                );
                let (body, step) = self.compile_matrix_component_step(
                    subject,
                    "_matrix_reduction_call",
                    &p.callable,
                    &p.body,
                    &p.application_well_defined,
                    position,
                )?;
                let continuation = self.compile_matrix_component_reduction(
                    &p.body,
                    &body,
                    &p.continuation,
                    endpoint,
                    &scope,
                )?;
                Ok(format!(
                    "(let _matrix_reduction_call := {call};\n  (show {value} = Litex.denote _matrix_reduction_call from rfl).trans ({step}.trans {continuation}))"
                ))
            }
            MatrixComponentReductionEvidence::ConjugateArgument(inner) => {
                let (
                    Obj::ComplexOperator(ComplexOperator::Conjugate(start)),
                    Obj::ComplexOperator(ComplexOperator::Conjugate(end)),
                ) = (subject, &proof.value)
                else {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/ConjugateReductionSubject",
                    ));
                };
                if inner.value.ir() != end.arg.ir() {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/ConjugateReductionEndpoint",
                    ));
                }
                let input = match &inner.evidence {
                    MatrixComponentReductionEvidence::NativeApplication(p) => {
                        ensure_object(&start.arg, &p.application_well_defined)?;
                        self.compile_wd(&p.application_well_defined, position)?
                    }
                    _ => self.compile_object_reference(&start.arg, position)?,
                };
                let output = self.compile_object_reference(&end.arg, position)?;
                let inner = self.compile_matrix_component_reduction(
                    &start.arg,
                    &format!("(Litex.denote {input})"),
                    inner,
                    &format!("(Litex.denote {output})"),
                    position,
                )?;
                let f = "(Litex.complexUnaryValue (M := M) (fun z : ℂ => star z))";
                Ok(format!(
                    "((show {value} = {f} (Litex.denote {input}) from rfl).trans ((congrArg {f} {inner}).trans (show {f} (Litex.denote {output}) = {endpoint} from rfl)))"
                ))
            }
        }
    }
}
