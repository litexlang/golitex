//! Replay callable matrix constructors through their original function signatures.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, MatrixCallableProof, MatrixCallableWellDefinedProof,
    MatrixFunctionScalarCarrierProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_callable_signature(
        &self,
        proof: &MatrixCallableProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let root = self.compile_matrix_callable_root(proof, position)?;
        Self::matrix_callable_signature_term(proof, &root)
    }

    pub(in crate::compile_to_lean) fn matrix_callable_signature_term(
        proof: &MatrixCallableProof,
        root: &str,
    ) -> Result<String, LeanCompileError> {
        match &proof.operator {
            MatrixOperator::Add(_)
            | MatrixOperator::Subtract(_)
            | MatrixOperator::Scale(_)
            | MatrixOperator::OuterProduct(_)
            | MatrixOperator::Multiply(_) => {
                let scalar = match proof.function.body.ret_set.as_ref() {
                    Obj::StandardSet(StandardSet::R) => "real",
                    Obj::StandardSet(StandardSet::C) => "complex",
                    _ => return Err(LeanCompileError::unsupported("Matrix/CallableCarrier")),
                };
                Ok(format!(
                    "(Litex.matrixEntrywiseSignature ({root}).val.rows ({root}).val.cols .{scalar})"
                ))
            }
            MatrixOperator::Apply(_) => {
                let scalar = match proof.function.body.ret_set.as_ref() {
                    Obj::StandardSet(StandardSet::C) => "complex",
                    Obj::StandardSet(StandardSet::R) => "real",
                    _ => return Err(LeanCompileError::unsupported("Matrix/ApplyOutput")),
                };
                Ok(format!(
                    "(Litex.matrixApplySignature ({root}).val.rows .{scalar})"
                ))
            }
            MatrixOperator::Minor(_) => {
                let scalar = match proof.function.body.ret_set.as_ref() {
                    Obj::StandardSet(StandardSet::R) => "real",
                    Obj::StandardSet(StandardSet::C) => "complex",
                    _ => return Err(LeanCompileError::unsupported("Matrix/MinorOutput")),
                };
                Ok(format!(
                    "(Litex.matrixMinorSignature ({root}).val.order .{scalar})"
                ))
            }
            MatrixOperator::Diagonal(_)
            | MatrixOperator::Power(_)
            | MatrixOperator::Adjugate(_)
            | MatrixOperator::Inverse(_) => {
                let scalar = match proof.function.body.ret_set.as_ref() {
                    Obj::StandardSet(StandardSet::R) => "real",
                    Obj::StandardSet(StandardSet::C) => "complex",
                    _ => return Err(LeanCompileError::unsupported("Matrix/CallableCarrier")),
                };
                Ok(format!(
                    "(Litex.matrixEntrywiseSignature ({root}).val.order ({root}).val.order .{scalar})"
                ))
            }
            MatrixOperator::ZeroMatrix(_) => Ok(format!(
                "(Litex.zeroMatrixSignature ({root}).val.rows ({root}).val.cols)"
            )),
            MatrixOperator::IdentityMatrix(_) => Ok(format!(
                "(Litex.identityMatrixSignature ({root}).val.order)"
            )),
            MatrixOperator::Transpose(_) | MatrixOperator::ConjugateTranspose(_) => {
                let scalar = match proof.function.body.ret_set.as_ref() {
                    Obj::StandardSet(StandardSet::R) => "real",
                    Obj::StandardSet(StandardSet::C) => "complex",
                    _ => return Err(LeanCompileError::unsupported("Matrix/CallableCarrier")),
                };
                Ok(format!(
                    "(Litex.matrixTransposeSignature ({root}).val.rows ({root}).val.cols .{scalar})"
                ))
            }
            _ => Err(LeanCompileError::unsupported("Matrix/CallableOperator")),
        }
    }

    pub(in crate::compile_to_lean) fn validate_matrix_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        if matches!(proof.operator, MatrixOperator::Inverse(_)) {
            return Self::validate_matrix_inverse_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Adjugate(_)) {
            return Self::validate_matrix_adjugate_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Minor(_)) {
            return Self::validate_matrix_minor_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Power(_)) {
            return Self::validate_matrix_power_callable(proof);
        }
        if matches!(
            proof.operator,
            MatrixOperator::Add(_) | MatrixOperator::Subtract(_)
        ) {
            return Self::validate_matrix_entrywise_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Apply(_)) {
            return Self::validate_matrix_apply_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Multiply(_)) {
            return Self::validate_matrix_multiply_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Scale(_)) {
            return Self::validate_matrix_scale_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::OuterProduct(_)) {
            return Self::validate_matrix_outer_callable(proof);
        }
        if matches!(proof.operator, MatrixOperator::Diagonal(_)) {
            return Self::validate_matrix_diagonal_callable(proof);
        }
        if let MatrixOperator::ZeroMatrix(m) = &proof.operator {
            if !matches!(
                proof.scalar_carrier,
                MatrixFunctionScalarCarrierProof::RealConstants
            ) || !is_exact_zero(&proof.function.equal_to)
            {
                return Err(LeanCompileError::unsupported("Matrix/CallableDefinition"));
            }
            return Self::validate_matrix_signature(
                &MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::R)),
                    rows: m.rows.clone(),
                    cols: m.cols.clone(),
                },
                &proof.function.body,
            );
        }
        if let MatrixOperator::IdentityMatrix(m) = &proof.operator {
            if !matches!(
                proof.scalar_carrier,
                MatrixFunctionScalarCarrierProof::RealConstants
            ) {
                return Err(LeanCompileError::unsupported("Matrix/CallableCarrier"));
            }
            Self::validate_matrix_signature(
                &MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::R)),
                    rows: m.order.clone(),
                    cols: m.order.clone(),
                },
                &proof.function.body,
            )?;
            let groups = &proof.function.body.set_bound_parameters.groups;
            let singleton = |index: usize| {
                Obj::SetFormer(SetFormer::ListSet(ListSet {
                    list: vec![Box::new(matrix_identifier(&groups[index].params[0]))],
                }))
            };
            let expected = Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
                set: Box::new(Obj::SetOperator(SetOperator::Intersect(Intersect {
                    left: Box::new(singleton(0)),
                    right: Box::new(singleton(1)),
                }))),
            }));
            if expected.ir() != proof.function.equal_to.ir() {
                return Err(LeanCompileError::unsupported("Matrix/CallableBody"));
            }
            return Ok(());
        }
        let (matrix, rows, cols) = match &proof.operator {
            MatrixOperator::Transpose(m) => (&m.matrix, &m.rows, &m.cols),
            MatrixOperator::ConjugateTranspose(m) => (&m.matrix, &m.rows, &m.cols),
            _ => return Err(LeanCompileError::unsupported("Matrix/CallableOperator")),
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealInput(checked) => {
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/RealInputSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported("Matrix/RealInputSignature"));
                };
                if f.element.ir() != matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/RealInputSubject"));
                }
                Self::validate_matrix_signature(
                    &MatrixSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        rows: rows.clone(),
                        cols: cols.clone(),
                    },
                    signature,
                )?;
                StandardSet::R
            }
            MatrixFunctionScalarCarrierProof::RealReturnedFunction(domain) => {
                Self::validate_matrix_signature(
                    &MatrixSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        rows: rows.clone(),
                        cols: cols.clone(),
                    },
                    &domain.signature,
                )?;
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/CallableCarrier")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: cols.clone(),
                cols: rows.clone(),
            },
            &proof.function.body,
        )?;
        let groups = &proof.function.body.set_bound_parameters.groups;
        let call = matrix_call(
            matrix,
            vec![
                matrix_identifier(&groups[1].params[0]),
                matrix_identifier(&groups[0].params[0]),
            ],
        );
        let expected = match &proof.operator {
            MatrixOperator::ConjugateTranspose(_) => {
                Obj::ComplexOperator(ComplexOperator::Conjugate(Conjugate {
                    arg: Box::new(call),
                }))
            }
            _ => call,
        };
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/CallableBody"));
        }

        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_callable_root(
        &self,
        proof: &MatrixCallableProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        Self::validate_matrix_callable(proof)?;
        let root = Obj::MatrixOperator(proof.operator.clone());
        match &proof.well_defined {
            MatrixCallableWellDefinedProof::Checked(wd) => {
                ensure_object(&root, wd)?;
                self.compile_wd(wd, position)
            }
            MatrixCallableWellDefinedProof::ParentAtomic => {
                self.compile_object_reference(&root, position)
            }
        }
    }

    pub(in crate::compile_to_lean) fn compile_matrix_callable_member(
        &self,
        subject: &Obj,
        proof: &MatrixCallableProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let root = self.compile_matrix_callable_root(proof, position)?;
        let root_obj = Obj::MatrixOperator(proof.operator.clone());
        let captured;
        let formed = match &proof.well_defined {
            MatrixCallableWellDefinedProof::Checked(wd) => {
                captured = SourcePosition::new(Some(position), SourceOwner::WD(wd), usize::MAX);
                &captured
            }
            MatrixCallableWellDefinedProof::ParentAtomic => position,
        };
        let target = if subject.ir() == root_obj.ir() {
            "_litex_matrix".to_string()
        } else {
            self.compile_object_reference(subject, formed)?
        };
        let same = self.compile_equality_path(subject, &root_obj, &proof.function_equal, formed)?;
        let signature = Self::matrix_callable_signature_term(proof, "_litex_matrix")?;
        let member = self.compile_matrix_root_member(proof, "_litex_matrix", formed)?;
        Ok(format!(
            "(let _litex_matrix := {root}; let _litex_matrix_signature := {signature}; Litex.inOfSame _litex_matrix {target} (Litex.fnSet _litex_matrix_signature) (Litex.fnSet _litex_matrix_signature) ({same}).symm (by rfl) {member})"
        ))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_root_member(
        &self,
        proof: &MatrixCallableProof,
        root: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        Self::validate_matrix_callable(proof)?;
        let name = match &proof.operator {
            MatrixOperator::Add(_) | MatrixOperator::Subtract(_) => "matrixEntrywise",
            MatrixOperator::Apply(_) => "matrixApply",
            MatrixOperator::Multiply(_) => "matrixMultiply",
            MatrixOperator::Power(_) => "matrixPower",
            MatrixOperator::Minor(_) => "matrixMinor",
            MatrixOperator::Adjugate(_) => "matrixAdjugate",
            MatrixOperator::Inverse(_) => "matrixInverse",
            MatrixOperator::Scale(_) => "matrixScale",
            MatrixOperator::OuterProduct(_) => "matrixOuter",
            MatrixOperator::Diagonal(_) => "matrixDiagonal",
            MatrixOperator::ZeroMatrix(_) => "zeroMatrix",
            MatrixOperator::IdentityMatrix(_) => "identityMatrix",
            MatrixOperator::Transpose(_) => "transpose",
            MatrixOperator::ConjugateTranspose(_) => "conjugateTranspose",
            _ => return Err(LeanCompileError::unsupported("Matrix/CallableOperator")),
        };
        let member = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::RealConstants
            | MatrixFunctionScalarCarrierProof::ComplexInput => {
                format!("(Litex.{name}InFnSet {root})")
            }
            MatrixFunctionScalarCarrierProof::RealOperands(operands) => {
                use crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof;
                let mut checked = Vec::new();
                for operand in operands {
                    let MatrixRealOperandProof::Membership(p) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/RealOperandRule"));
                    };
                    checked.push(self.compile_verify(p, position)?.1);
                }
                format!("(Litex.{name}InRealFnSet {root} {})", checked.join(" "))
            }
            MatrixFunctionScalarCarrierProof::RealInput(checked) => {
                let h = self.compile_verify(checked, position)?.1;
                format!("(Litex.{name}InRealFnSet {root} {h})")
            }
            MatrixFunctionScalarCarrierProof::RealReturnedFunction(domain) => {
                let input = match &proof.operator {
                    MatrixOperator::Transpose(m) => m.matrix.as_ref(),
                    MatrixOperator::ConjugateTranspose(m) => m.matrix.as_ref(),
                    _ => return Err(LeanCompileError::unsupported("Matrix/ReturnedRealOperator")),
                };
                let h = self.compile_complete_domain_member(input, domain, position)?;
                format!("(Litex.{name}InRealFnSet {root} {h})")
            }
        };
        Ok(member)
    }
}
