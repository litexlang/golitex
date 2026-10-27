//! Replay the native inverse formula and original square-matrix carrier evidence.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof;
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_identifier, MatrixCallableProof, MatrixFunctionScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_matrix_inverse_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Inverse(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/InverseOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 1 => {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/InverseRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/InverseRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported("Matrix/InverseRealSignature"));
                };
                if f.element.ir() != m.matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/InverseRealMatrix"));
                }
                Self::validate_matrix_signature(
                    &MatrixSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        rows: m.order.clone(),
                        cols: m.order.clone(),
                    },
                    signature,
                )?;
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/InverseCarrier")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: m.order.clone(),
                cols: m.order.clone(),
            },
            &proof.function.body,
        )?;
        let groups = &proof.function.body.set_bound_parameters.groups;
        let row = matrix_identifier(&groups[0].params[0]);
        let col = matrix_identifier(&groups[1].params[0]);
        let cofactor = Obj::MatrixOperator(MatrixOperator::Cofactor(MatrixCofactor {
            matrix: m.matrix.clone(),
            order: m.order.clone(),
            row: Box::new(col),
            col: Box::new(row),
        }));
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
            left: Box::new(cofactor),
            right: Box::new(Obj::MatrixOperator(MatrixOperator::Determinant(
                Determinant {
                    matrix: m.matrix.clone(),
                    order: m.order.clone(),
                },
            ))),
        }));
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/InverseBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_inverse_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Inverse(m), MatrixOperatorObjWellDefinedProofByDef::Inverse(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/InverseWD"));
        };
        if p.child_obj_well_defined.len() != 2 || p.requirement_fact_verified.len() != 3 {
            return Err(LeanCompileError::unsupported("Matrix/InverseWDStages"));
        }
        for (index, subject) in [&m.order, &m.matrix].iter().enumerate() {
            let expected = if index == 0 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: m.order.clone(),
                    cols: m.order.clone(),
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/InverseWDPremise"));
            }
        }
        let determinant = Obj::MatrixOperator(MatrixOperator::Determinant(Determinant {
            matrix: m.matrix.clone(),
            order: m.order.clone(),
        }));
        if !matches!(source_subject(&p.requirement_fact_verified[2])?,
            Fact::AtomicFact(AtomicFact::NotEqualFact(f))
                if f.left.ir() == determinant.ir() && is_exact_zero(&f.right))
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/InverseNonzeroDeterminant",
            ));
        }
        let mut arguments = Vec::new();
        for (index, subject) in [&m.matrix, &m.order].iter().enumerate() {
            ensure_object(subject, &p.child_obj_well_defined[index])?;
            arguments.push(self.compile_wd(
                &p.child_obj_well_defined[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, proof) in p.requirement_fact_verified.iter().enumerate() {
            arguments.push(self.compile_wd_requirement(
                proof,
                &SourcePosition {
                    before: 2 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixInverse {})", arguments.join(" ")))
    }
}
