//! Replay outer products of the source's complete finite vector functions.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::MatrixRealOperandProof;
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, MatrixCallableProof, MatrixFunctionScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_matrix_outer_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::OuterProduct(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/OuterOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 2 => {
                for (operand, (vector, size)) in operands
                    .iter()
                    .zip([(&m.left, &m.rows), (&m.right, &m.cols)])
                {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/OuterRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported("Matrix/OuterRealSubject"));
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                        return Err(LeanCompileError::unsupported("Matrix/OuterRealSignature"));
                    };
                    if f.element.ir() != vector.ir() {
                        return Err(LeanCompileError::unsupported("Matrix/OuterRealVector"));
                    }
                    Self::validate_finite_seq_signature(
                        &FiniteSeqSet {
                            set: Box::new(Obj::StandardSet(StandardSet::R)),
                            n: size.clone(),
                        },
                        signature,
                    )?;
                }
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/OuterCarrier")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: m.rows.clone(),
                cols: m.cols.clone(),
            },
            &proof.function.body,
        )?;
        let groups = &proof.function.body.set_bound_parameters.groups;
        let left = matrix_call(&m.left, vec![matrix_identifier(&groups[0].params[0])]);
        let right = matrix_call(&m.right, vec![matrix_identifier(&groups[1].params[0])]);
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(left),
            right: Box::new(right),
        }));
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/OuterBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_outer_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            MatrixOperator::OuterProduct(m),
            MatrixOperatorObjWellDefinedProofByDef::OuterProduct(p),
        ) = (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/OuterWD"));
        };
        if p.child_obj_well_defined.len() != 4 || p.requirement_fact_verified.len() != 4 {
            return Err(LeanCompileError::unsupported("Matrix/OuterWDStages"));
        }
        for (index, subject) in [&m.rows, &m.cols, &m.left, &m.right].iter().enumerate() {
            let expected = if index < 2 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: if index == 2 {
                        m.rows.clone()
                    } else {
                        m.cols.clone()
                    },
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/OuterWDPremise"));
            }
        }
        let mut arguments = Vec::new();
        for (index, subject) in [&m.left, &m.right, &m.rows, &m.cols].iter().enumerate() {
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
                    before: 4 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixOuter {})", arguments.join(" ")))
    }
}
