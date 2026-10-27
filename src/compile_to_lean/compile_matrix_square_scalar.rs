//! Shared square-matrix WD and real-input evidence for trace and determinant.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_square_scalar_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, matrix, order, children, requirements) = match (operator, proof) {
            (MatrixOperator::Trace(m), MatrixOperatorObjWellDefinedProofByDef::Trace(p)) => (
                "matrixTrace",
                &m.matrix,
                &m.order,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            (
                MatrixOperator::Determinant(m),
                MatrixOperatorObjWellDefinedProofByDef::Determinant(p),
            ) => (
                "matrixDeterminant",
                &m.matrix,
                &m.order,
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            _ => return Err(LeanCompileError::unsupported("Matrix/SquareScalarWD")),
        };
        if children.len() != 2 || requirements.len() != 2 {
            return Err(LeanCompileError::unsupported("Matrix/SquareScalarWDStages"));
        }
        if !matches!(source_subject(&requirements[0])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==order.ir() && f.set==Obj::StandardSet(StandardSet::N))
            || !matches!(source_subject(&requirements[1])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==matrix.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(s)) if s.set.as_ref()==&Obj::StandardSet(StandardSet::C) && s.rows.ir()==order.ir() && s.cols.ir()==order.ir()))
        {
            return Err(LeanCompileError::unsupported(
                "Matrix/SquareScalarWDPremise",
            ));
        }
        let mut args = Vec::new();
        for (i, obj) in [matrix, order].iter().enumerate() {
            ensure_object(obj, &children[i])?;
            args.push(self.compile_wd(
                &children[i],
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?);
        }
        for (i, p) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                p,
                &SourcePosition {
                    before: 2 + i,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_square_scalar_real(
        &self,
        subject: &Obj,
        checked: &VerifyFactResult,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, matrix, order) = match subject {
            Obj::MatrixOperator(MatrixOperator::Trace(m)) => {
                ("matrixTraceInR", &m.matrix, &m.order)
            }
            Obj::MatrixOperator(MatrixOperator::Determinant(m)) => {
                ("matrixDeterminantInR", &m.matrix, &m.order)
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/SquareScalarSubject")),
        };
        let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
            return Err(LeanCompileError::unsupported(
                "Matrix/SquareScalarRealSubject",
            ));
        };
        if f.element.ir() != matrix.ir() {
            return Err(LeanCompileError::unsupported(
                "Matrix/SquareScalarRealMatrix",
            ));
        }
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
            return Err(LeanCompileError::unsupported(
                "Matrix/SquareScalarRealSignature",
            ));
        };
        Self::validate_matrix_signature(
            &MatrixSet {
                set: Box::new(Obj::StandardSet(StandardSet::R)),
                rows: order.clone(),
                cols: order.clone(),
            },
            signature,
        )?;
        let root = self.compile_object_reference(subject, position)?;
        let member = self.compile_verify(checked, position)?.1;
        Ok(format!("(Litex.{name} {root} {member})"))
    }
}
