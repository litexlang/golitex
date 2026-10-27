//! Replay a matrix applied to a finite vector using its captured summand.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{index_set, MatrixRealOperandProof};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, MatrixCallableProof, MatrixFunctionScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;
impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_matrix_apply_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Apply(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/ApplyOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 2 => {
                for (index, operand) in operands.iter().enumerate() {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/ApplyRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported("Matrix/ApplyRealSubject"));
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                        return Err(LeanCompileError::unsupported("Matrix/ApplyRealSignature"));
                    };
                    let expected = if index == 0 { &m.matrix } else { &m.vector };
                    if f.element.ir() != expected.ir() {
                        return Err(LeanCompileError::unsupported("Matrix/ApplyRealOperand"));
                    }
                    if index == 0 {
                        Self::validate_matrix_signature(
                            &MatrixSet {
                                set: Box::new(Obj::StandardSet(StandardSet::R)),
                                rows: m.rows.clone(),
                                cols: m.cols.clone(),
                            },
                            signature,
                        )?;
                    } else {
                        Self::validate_finite_seq_signature(
                            &FiniteSeqSet {
                                set: Box::new(Obj::StandardSet(StandardSet::R)),
                                n: m.cols.clone(),
                            },
                            signature,
                        )?;
                    }
                }
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/ApplyCarrier")),
        };
        Self::validate_finite_seq_signature(
            &FiniteSeqSet {
                set: Box::new(Obj::StandardSet(scalar)),
                n: m.rows.clone(),
            },
            &proof.function.body,
        )?;
        let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
            proof.function.equal_to.as_ref()
        else {
            return Err(LeanCompileError::unsupported("Matrix/ApplySum"));
        };
        if sum.set.ir() != index_set(&m.cols).ir() {
            return Err(LeanCompileError::unsupported("Matrix/ApplyIndices"));
        }
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/ApplyIterand"));
        };
        let groups = &f.body.set_bound_parameters.groups;
        if groups.len() != 1
            || groups[0].params.len() != 1
            || groups[0].param_type.ir() != sum.set.ir()
            || !f.body.dom_facts.is_empty()
            || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/ApplyIterandSignature",
            ));
        }
        let k = matrix_identifier(&groups[0].params[0]);
        let row = matrix_identifier(&proof.function.body.set_bound_parameters.groups[0].params[0]);
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(matrix_call(&m.matrix, vec![row, k.clone()])),
            right: Box::new(matrix_call(&m.vector, vec![k])),
        }));
        if expected.ir() != f.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/ApplyBody"));
        }
        Ok(())
    }
    pub(in crate::compile_to_lean) fn compile_matrix_apply_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Apply(m), MatrixOperatorObjWellDefinedProofByDef::Apply(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/ApplyWD"));
        };
        if p.child_obj_well_defined.len() != 4 || p.requirement_fact_verified.len() != 4 {
            return Err(LeanCompileError::unsupported("Matrix/ApplyWDStages"));
        }
        for (index, subject) in [&m.rows, &m.cols, &m.matrix, &m.vector].iter().enumerate() {
            let expected = match index {
                0 | 1 => Obj::StandardSet(StandardSet::N),
                2 => Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: m.rows.clone(),
                    cols: m.cols.clone(),
                })),
                _ => Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: m.cols.clone(),
                })),
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/ApplyWDPremise"));
            }
        }
        let mut args = Vec::new();
        for (index, subject) in [&m.matrix, &m.vector, &m.rows, &m.cols].iter().enumerate() {
            ensure_object(subject, &p.child_obj_well_defined[index])?;
            args.push(self.compile_wd(
                &p.child_obj_well_defined[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, checked) in p.requirement_fact_verified.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                checked,
                &SourcePosition {
                    before: 4 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixApply {})", args.join(" ")))
    }
}
