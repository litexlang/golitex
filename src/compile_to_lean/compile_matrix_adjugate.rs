//! Replay the native adjugate formula and original square-matrix carrier evidence.
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
    pub(in crate::compile_to_lean) fn validate_matrix_adjugate_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Adjugate(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/AdjugateOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 1 => {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/AdjugateRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/AdjugateRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/AdjugateRealSignature",
                    ));
                };
                if f.element.ir() != m.matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/AdjugateRealMatrix"));
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
            _ => return Err(LeanCompileError::unsupported("Matrix/AdjugateCarrier")),
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
        let expected = Obj::MatrixOperator(MatrixOperator::Cofactor(MatrixCofactor {
            matrix: m.matrix.clone(),
            order: m.order.clone(),
            row: Box::new(col),
            col: Box::new(row),
        }));
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/AdjugateBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_adjugate_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Adjugate(m), MatrixOperatorObjWellDefinedProofByDef::Adjugate(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/AdjugateWD"));
        };
        if p.child_obj_well_defined.len() != 2 || p.requirement_fact_verified.len() != 2 {
            return Err(LeanCompileError::unsupported("Matrix/AdjugateWDStages"));
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
                return Err(LeanCompileError::unsupported("Matrix/AdjugateWDPremise"));
            }
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
        Ok(format!("(Litex.matrixAdjugate {})", arguments.join(" ")))
    }
}
