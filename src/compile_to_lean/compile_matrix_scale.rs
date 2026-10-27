//! Replay matrix scalar multiplication with its original scalar and domain proofs.
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
    pub(in crate::compile_to_lean) fn validate_matrix_scale_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Scale(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/ScaleOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 2 => {
                for (index, operand) in operands.iter().enumerate() {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/ScaleRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported("Matrix/ScaleRealSubject"));
                    };
                    if index == 0 {
                        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                            return Err(LeanCompileError::unsupported("Matrix/ScaleRealSignature"));
                        };
                        if f.element.ir() != m.matrix.ir() {
                            return Err(LeanCompileError::unsupported("Matrix/ScaleRealMatrix"));
                        }
                        Self::validate_matrix_signature(
                            &MatrixSet {
                                set: Box::new(Obj::StandardSet(StandardSet::R)),
                                rows: m.rows.clone(),
                                cols: m.cols.clone(),
                            },
                            signature,
                        )?;
                    } else if f.element.ir() != m.scalar.ir()
                        || f.set != Obj::StandardSet(StandardSet::R)
                    {
                        return Err(LeanCompileError::unsupported("Matrix/ScaleRealScalar"));
                    }
                }
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/ScaleCarrier")),
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
        let application = matrix_call(
            &m.matrix,
            vec![
                matrix_identifier(&groups[0].params[0]),
                matrix_identifier(&groups[1].params[0]),
            ],
        );
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: m.scalar.clone(),
            right: Box::new(application),
        }));
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/ScaleBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_scale_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Scale(m), MatrixOperatorObjWellDefinedProofByDef::Scale(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/ScaleWD"));
        };
        if p.child_obj_well_defined.len() != 4 || p.requirement_fact_verified.len() != 4 {
            return Err(LeanCompileError::unsupported("Matrix/ScaleWDStages"));
        }
        for (index, subject) in [&m.scalar, &m.rows, &m.cols, &m.matrix].iter().enumerate() {
            let expected = match index {
                0 => Obj::StandardSet(StandardSet::C),
                1 | 2 => Obj::StandardSet(StandardSet::N),
                _ => Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: m.rows.clone(),
                    cols: m.cols.clone(),
                })),
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/ScaleWDPremise"));
            }
        }
        let mut arguments = Vec::new();
        for (index, subject) in [&m.scalar, &m.matrix, &m.rows, &m.cols].iter().enumerate() {
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
        Ok(format!("(Litex.matrixScale {})", arguments.join(" ")))
    }
}
