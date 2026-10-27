//! Replay the native pointwise matrix signature, body and ordered WD premises.
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
    pub(in crate::compile_to_lean) fn validate_matrix_entrywise_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let (left, right, rows, cols, subtract) = match &proof.operator {
            MatrixOperator::Add(p) => (&p.left, &p.right, &p.rows, &p.cols, false),
            MatrixOperator::Subtract(p) => (&p.left, &p.right, &p.rows, &p.cols, true),
            _ => return Err(LeanCompileError::unsupported("Matrix/EntrywiseOperator")),
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 2 => {
                for (operand, source) in operands.iter().zip([left, right]) {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/EntrywiseRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported("Matrix/EntrywiseRealSubject"));
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                        return Err(LeanCompileError::unsupported(
                            "Matrix/EntrywiseRealSignature",
                        ));
                    };
                    if f.element.ir() != source.ir() {
                        return Err(LeanCompileError::unsupported("Matrix/EntrywiseRealSubject"));
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
            _ => return Err(LeanCompileError::unsupported("Matrix/EntrywiseCarrier")),
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: rows.clone(),
                cols: cols.clone(),
            },
            &proof.function.body,
        )?;
        let groups = &proof.function.body.set_bound_parameters.groups;
        let args = vec![
            matrix_identifier(&groups[0].params[0]),
            matrix_identifier(&groups[1].params[0]),
        ];
        let a = Box::new(matrix_call(left, args.clone()));
        let b = Box::new(matrix_call(right, args));
        let expected = Obj::ArithmeticOperator(if subtract {
            ArithmeticOperator::Sub(Sub { left: a, right: b })
        } else {
            ArithmeticOperator::Add(Add { left: a, right: b })
        });
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/EntrywiseBody"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_entrywise_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left, right, rows, cols, operation, children, requirements) = match (operator, proof) {
            (MatrixOperator::Add(m), MatrixOperatorObjWellDefinedProofByDef::Add(p)) => (
                &m.left,
                &m.right,
                &m.rows,
                &m.cols,
                "add",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            (MatrixOperator::Subtract(m), MatrixOperatorObjWellDefinedProofByDef::Subtract(p)) => (
                &m.left,
                &m.right,
                &m.rows,
                &m.cols,
                "sub",
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            _ => return Err(LeanCompileError::unsupported("Matrix/EntrywiseWD")),
        };
        if children.len() != 4 || requirements.len() != 4 {
            return Err(LeanCompileError::unsupported("Matrix/EntrywiseWDStages"));
        }
        for (index, subject) in [rows, cols, left, right].iter().enumerate() {
            let expected = if index < 2 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: rows.clone(),
                    cols: cols.clone(),
                }))
            };
            if !matches!(source_subject(&requirements[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/EntrywiseWDPremise"));
            }
        }
        let mut arguments = Vec::new();
        for (index, subject) in [left, right, rows, cols].iter().enumerate() {
            ensure_object(subject, &children[index])?;
            arguments.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, proof) in requirements.iter().enumerate() {
            arguments.push(self.compile_wd_requirement(
                proof,
                &SourcePosition {
                    before: 4 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!(
            "(Litex.matrixEntrywise .{operation} {})",
            arguments.join(" ")
        ))
    }
}
