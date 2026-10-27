//! Replay matrix products from compatible domains and the recorded finite summand.
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
    pub(in crate::compile_to_lean) fn validate_matrix_multiply_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Multiply(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 2 => {
                for (operand, (matrix, rows, cols)) in operands
                    .iter()
                    .zip([(&m.left, &m.rows, &m.inner), (&m.right, &m.inner, &m.cols)])
                {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/MultiplyRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported("Matrix/MultiplyRealSubject"));
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                        return Err(LeanCompileError::unsupported(
                            "Matrix/MultiplyRealSignature",
                        ));
                    };
                    if f.element.ir() != matrix.ir() {
                        return Err(LeanCompileError::unsupported("Matrix/MultiplyRealOperand"));
                    }
                    Self::validate_matrix_signature(
                        &MatrixSet {
                            set: Box::new(Obj::StandardSet(StandardSet::R)),
                            rows: rows.clone(),
                            cols: cols.clone(),
                        },
                        signature,
                    )?;
                }
                StandardSet::R
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/MultiplyCarrier")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: m.rows.clone(),
                cols: m.cols.clone(),
            },
            &proof.function.body,
        )?;
        let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
            proof.function.equal_to.as_ref()
        else {
            return Err(LeanCompileError::unsupported("Matrix/MultiplySum"));
        };
        if sum.set.ir() != index_set(&m.inner).ir() {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyIndices"));
        }
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyIterand"));
        };
        let groups = &f.body.set_bound_parameters.groups;
        if groups.len() != 1
            || groups[0].params.len() != 1
            || groups[0].param_type.ir() != sum.set.ir()
            || !f.body.dom_facts.is_empty()
            || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/MultiplyIterandSignature",
            ));
        }
        let outer = &proof.function.body.set_bound_parameters.groups;
        let k = matrix_identifier(&groups[0].params[0]);
        let left = matrix_call(
            &m.left,
            vec![matrix_identifier(&outer[0].params[0]), k.clone()],
        );
        let right = matrix_call(&m.right, vec![k, matrix_identifier(&outer[1].params[0])]);
        let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
            left: Box::new(left),
            right: Box::new(right),
        }));
        if expected.ir() != f.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyBody"));
        }
        Ok(())
    }
    pub(in crate::compile_to_lean) fn compile_matrix_multiply_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Multiply(m), MatrixOperatorObjWellDefinedProofByDef::Multiply(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyWD"));
        };
        if p.child_obj_well_defined.len() != 5 || p.requirement_fact_verified.len() != 5 {
            return Err(LeanCompileError::unsupported("Matrix/MultiplyWDStages"));
        }
        for (index, subject) in [&m.rows, &m.inner, &m.cols, &m.left, &m.right]
            .iter()
            .enumerate()
        {
            let expected = if index < 3 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: if index == 3 {
                        m.rows.clone()
                    } else {
                        m.inner.clone()
                    },
                    cols: if index == 3 {
                        m.inner.clone()
                    } else {
                        m.cols.clone()
                    },
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/MultiplyWDPremise"));
            }
        }
        let mut args = Vec::new();
        for (index, subject) in [&m.left, &m.right, &m.rows, &m.inner, &m.cols]
            .iter()
            .enumerate()
        {
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
                    before: 5 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixMultiply {})", args.join(" ")))
    }
}
