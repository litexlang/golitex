//! Replay deleted-row/column matrices with their original index and size evidence.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{
    add, div, index_set, sub, MatrixRealOperandProof,
};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, matrix_number, matrix_space, MatrixCallableProof,
    MatrixFunctionScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_deleted_index_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, matrix, order, row, col, children, requirements) = match (operator, proof) {
            (MatrixOperator::Minor(m), MatrixOperatorObjWellDefinedProofByDef::Minor(p)) => (
                "matrixMinor",
                &m.matrix,
                &m.order,
                &m.row,
                &m.col,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            (MatrixOperator::Cofactor(m), MatrixOperatorObjWellDefinedProofByDef::Cofactor(p)) => (
                "matrixCofactor",
                &m.matrix,
                &m.order,
                &m.row,
                &m.col,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            _ => return Err(LeanCompileError::unsupported("Matrix/DeletedIndexWD")),
        };
        if children.len() != 4 || requirements.len() != 5 {
            return Err(LeanCompileError::unsupported("Matrix/DeletedIndexWDStages"));
        }
        let expected = [
            (order.as_ref(), Obj::StandardSet(StandardSet::NPos)),
            (row.as_ref(), index_set(order)),
            (col.as_ref(), index_set(order)),
            (order.as_ref(), Obj::StandardSet(StandardSet::N)),
            (
                matrix.as_ref(),
                matrix_space(
                    Obj::StandardSet(StandardSet::C),
                    *order.clone(),
                    *order.clone(),
                ),
            ),
        ];
        for ((subject, set), checked) in expected.iter().zip(requirements) {
            if !matches!(source_subject(checked)?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==set.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/DeletedIndexWDPremise",
                ));
            }
        }
        let mut args = Vec::new();
        for (index, subject) in [matrix, order, row, col].iter().enumerate() {
            ensure_object(subject, &children[index])?;
            args.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, checked) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                checked,
                &SourcePosition {
                    before: 4 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn validate_matrix_minor_callable(
        proof: &MatrixCallableProof,
    ) -> Result<(), LeanCompileError> {
        let MatrixOperator::Minor(m) = &proof.operator else {
            return Err(LeanCompileError::unsupported("Matrix/MinorOperator"));
        };
        let scalar = match &proof.scalar_carrier {
            MatrixFunctionScalarCarrierProof::ComplexInput => StandardSet::C,
            MatrixFunctionScalarCarrierProof::RealOperands(operands) if operands.len() == 1 => {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/MinorRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/MinorRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported("Matrix/MinorRealSignature"));
                };
                if f.element.ir() != m.matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/MinorRealOperand"));
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
            _ => return Err(LeanCompileError::unsupported("Matrix/MinorCarrier")),
        };
        let size = Box::new(sub(*m.order.clone(), matrix_number(1)));
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(scalar)),
                rows: size.clone(),
                cols: size,
            },
            &proof.function.body,
        )?;
        let groups = &proof.function.body.set_bound_parameters.groups;
        let skip = |index: Obj, deleted: &Obj| {
            let shift = Obj::ArithmeticOperator(ArithmeticOperator::Floor(Floor {
                arg: Box::new(div(
                    sub(add(index.clone(), *m.order.clone()), deleted.clone()),
                    *m.order.clone(),
                )),
            }));
            add(index, shift)
        };
        let expected = matrix_call(
            &m.matrix,
            vec![
                skip(matrix_identifier(&groups[0].params[0]), &m.row),
                skip(matrix_identifier(&groups[1].params[0]), &m.col),
            ],
        );
        if expected.ir() != proof.function.equal_to.ir() {
            return Err(LeanCompileError::unsupported("Matrix/MinorBody"));
        }
        Ok(())
    }
}
