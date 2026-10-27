//! Replay the native diagonal-matrix delta and original vector carrier evidence.
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
    pub(in crate::compile_to_lean) fn validate_matrix_diagonal_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Diagonal(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/DiagonalOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 1 => {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/DiagonalRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/DiagonalRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/DiagonalRealSignature",
                    ));
                };
                if f.element.ir() != m.vector.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/DiagonalRealVector"));
                }
                Self::validate_finite_seq_signature(
                    &FiniteSeqSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        n: m.order.clone(),
                    },
                    signature,
                )?;
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/DiagonalCarrier")),
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
        let singleton = |x| {
            Obj::SetFormer(SetFormer::ListSet(ListSet {
                list: vec![Box::new(x)],
            }))
        };
        let delta = Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
            set: Box::new(Obj::SetOperator(SetOperator::Intersect(Intersect {
                left: Box::new(singleton(row.clone())),
                right: Box::new(singleton(col)),
            }))),
        }));
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(delta),
            right: Box::new(matrix_call(&m.vector, vec![row])),
        }));
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/DiagonalBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_diagonal_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Diagonal(m), MatrixOperatorObjWellDefinedProofByDef::Diagonal(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/DiagonalWD"));
        };
        if p.child_obj_well_defined.len() != 2 || p.requirement_fact_verified.len() != 2 {
            return Err(LeanCompileError::unsupported("Matrix/DiagonalWDStages"));
        }
        for (index, subject) in [&m.order, &m.vector].iter().enumerate() {
            let expected = if index == 0 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: m.order.clone(),
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/DiagonalWDPremise"));
            }
        }
        let mut arguments = Vec::new();
        for (index, subject) in [&m.vector, &m.order].iter().enumerate() {
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
        Ok(format!("(Litex.matrixDiagonal {})", arguments.join(" ")))
    }
}
