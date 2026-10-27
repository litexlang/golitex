//! Replay natural matrix powers and their recorded callable formula.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{
    anonymous, finite_sum, identity, index_set, matrix_multiply, mul, natural_literal,
    MatrixRealOperandProof,
};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, matrix_number, matrix_space, MatrixCallableProof,
    MatrixFunctionScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_power_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (MatrixOperator::Power(m), MatrixOperatorObjWellDefinedProofByDef::Power(p)) =
            (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/PowerWD"));
        };
        if p.child_obj_well_defined.len() != 3 || p.requirement_fact_verified.len() != 3 {
            return Err(LeanCompileError::unsupported("Matrix/PowerWDStages"));
        }
        for (index, subject) in [&m.order, &m.exponent, &m.matrix].iter().enumerate() {
            let set = if index < 2 {
                Obj::StandardSet(StandardSet::N)
            } else {
                matrix_space(
                    Obj::StandardSet(StandardSet::C),
                    *m.order.clone(),
                    *m.order.clone(),
                )
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==set.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/PowerWDPremise"));
            }
        }
        let mut args = Vec::new();
        for (index, subject) in [&m.matrix, &m.order, &m.exponent].iter().enumerate() {
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
                    before: 3 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixPower {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn validate_matrix_power_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Power(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/PowerOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 1 => {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerRealSignature"));
                };
                if f.element.ir() != m.matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/PowerRealOperand"));
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
            _ => return Err(LeanCompileError::unsupported("Matrix/PowerCarrier")),
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
        let expected = match natural_literal(&m.exponent) {
            Some(0) => matrix_call(&identity(*m.order.clone()), vec![row, col]),
            Some(k) => {
                let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) =
                    proof.function.equal_to.as_ref()
                else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerSum"));
                };
                let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerIterand"));
                };
                let binders = &f.body.set_bound_parameters.groups;
                if binders.len() != 1 || binders[0].params.len() != 1 {
                    return Err(LeanCompileError::unsupported("Matrix/PowerSumBinder"));
                }
                let index = binders[0].params[0].clone();
                let j = matrix_identifier(&index);
                let previous = Obj::MatrixOperator(MatrixOperator::Power(MatrixPower {
                    matrix: m.matrix.clone(),
                    order: m.order.clone(),
                    exponent: Box::new(matrix_number(k - 1)),
                }));
                finite_sum(
                    index_set(&m.order),
                    anonymous(
                        vec![(index, index_set(&m.order))],
                        Obj::StandardSet(StandardSet::C),
                        mul(
                            matrix_call(&previous, vec![row, j.clone()]),
                            matrix_call(&m.matrix, vec![j, col]),
                        ),
                    ),
                )
            }
            None => {
                let Obj::FnObj(call) = proof.function.equal_to.as_ref() else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerFoldCall"));
                };
                let FnObjHead::Object(head) = call.head.as_ref() else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerFoldHead"));
                };
                let Obj::IteratedOperator(IteratedOperator::Reduce(fold)) = head.as_ref() else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerFold"));
                };
                let (
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)),
                    Obj::FunctionSpace(FunctionSpace::AnonymousFn(op)),
                ) = (fold.func.as_ref(), fold.op.as_ref())
                else {
                    return Err(LeanCompileError::unsupported("Matrix/PowerFoldFunctions"));
                };
                let fb = &f.body.set_bound_parameters.groups;
                let ob = &op.body.set_bound_parameters.groups;
                if fb.len() != 1
                    || fb[0].params.len() != 1
                    || ob.len() != 2
                    || ob.iter().any(|g| g.params.len() != 1)
                {
                    return Err(LeanCompileError::unsupported("Matrix/PowerFoldBinders"));
                }
                let carrier = matrix_space(
                    Obj::StandardSet(StandardSet::C),
                    *m.order.clone(),
                    *m.order.clone(),
                );
                let folded = Obj::IteratedOperator(IteratedOperator::Reduce(Reduce {
                    start: Box::new(matrix_number(1)),
                    end: m.exponent.clone(),
                    func: Box::new(anonymous(
                        vec![(fb[0].params[0].clone(), Obj::StandardSet(StandardSet::Z))],
                        carrier.clone(),
                        *m.matrix.clone(),
                    )),
                    op: Box::new(anonymous(
                        vec![
                            (ob[0].params[0].clone(), carrier.clone()),
                            (ob[1].params[0].clone(), carrier.clone()),
                        ],
                        carrier,
                        matrix_multiply(
                            matrix_identifier(&ob[0].params[0]),
                            matrix_identifier(&ob[1].params[0]),
                            *m.order.clone(),
                            *m.order.clone(),
                            *m.order.clone(),
                        ),
                    )),
                    seed: Box::new(identity(*m.order.clone())),
                }));
                matrix_call(&folded, vec![row, col])
            }
        };
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/PowerBody"));
        }
        Ok(())
    }
}
