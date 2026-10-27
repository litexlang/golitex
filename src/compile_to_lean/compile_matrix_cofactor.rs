//! Replay cofactor carrier evidence and the original small-order scalar expansion.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{
    neg, MatrixCofactorScalarProof, MatrixRealOperandProof, MatrixScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_number, MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_cofactor_member(
        &self,
        fact: &InFact,
        proof: &MatrixCofactorScalarProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::MatrixOperator(MatrixOperator::Cofactor(m)) = &fact.element else {
            return Err(LeanCompileError::unsupported("Matrix/CofactorSubject"));
        };
        let root = self.compile_object_reference(&fact.element, position)?;
        match &proof.carrier {
            MatrixScalarCarrierProof::StandardSubset
                if fact.set == Obj::StandardSet(StandardSet::C) =>
            {
                Ok(format!("(Litex.matrixCofactorInC {root})"))
            }
            MatrixScalarCarrierProof::RealInputs(operands)
                if operands.len() == 1 && fact.set == Obj::StandardSet(StandardSet::R) =>
            {
                let MatrixRealOperandProof::Membership(checked) = &operands[0] else {
                    return Err(LeanCompileError::unsupported("Matrix/CofactorRealRule"));
                };
                let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                    return Err(LeanCompileError::unsupported("Matrix/CofactorRealSubject"));
                };
                let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/CofactorRealSignature",
                    ));
                };
                if f.element.ir() != m.matrix.ir() {
                    return Err(LeanCompileError::unsupported("Matrix/CofactorRealOperand"));
                }
                Self::validate_matrix_signature(
                    &MatrixSet {
                        set: Box::new(Obj::StandardSet(StandardSet::R)),
                        rows: m.order.clone(),
                        cols: m.order.clone(),
                    },
                    signature,
                )?;
                let member = self.compile_verify(checked, position)?.1;
                Ok(format!("(Litex.matrixCofactorInR {root} {member})"))
            }
            _ => Err(LeanCompileError::unsupported("Matrix/CofactorCarrier")),
        }
    }

    pub(in crate::compile_to_lean) fn compile_matrix_cofactor_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixScalarDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let MatrixDefinitionResidualProof::Verified(residual) = proof.equality.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/CofactorResidual"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported(
                "Matrix/CofactorResidualSubject",
            ));
        };
        if equal.left.ir() != proof.expression.ir() {
            return Err(LeanCompileError::unsupported(
                "Matrix/CofactorResidualEndpoint",
            ));
        }
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::MatrixOperator(MatrixOperator::Cofactor(m)) = native else {
                continue;
            };
            if equal.right.ir() != other.ir() {
                continue;
            }
            if ![&m.order, &m.row, &m.col]
                .iter()
                .all(|x| matches!(x.as_ref(), Obj::Literal(Literal::Number(_))))
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/CofactorLiteralIndices",
                ));
            }
            let (name, expression, domain, normalize) = match (
                closed_integer(&m.order),
                closed_integer(&m.row),
                closed_integer(&m.col),
            ) {
                (Some(1), Some(1), Some(1)) => {
                    ("matrixCofactorOne".to_string(), matrix_number(1), "", "")
                }
                (Some(2), Some(r @ 1..=2), Some(c @ 1..=2)) => {
                    let entry = matrix_call(
                        &m.matrix,
                        vec![matrix_number((3 - r) as i64), matrix_number((3 - c) as i64)],
                    );
                    (
                        format!("matrixCofactorTwo{r}{c}"),
                        if (r + c) % 2 == 0 { entry } else { neg(entry) },
                        " _cofactor.wd.2.2.2.2",
                        match (r, c) {
                            (1, 1) => {
                                "\n    simp only [Litex.matrixEntryValue, Nat.cast_ofNat] at _raw"
                            }
                            (2, 2) => {
                                "\n    simp only [Litex.matrixEntryValue, Nat.cast_one] at _raw"
                            }
                            _ => {
                                "\n    simp only [Litex.matrixEntryValue, Nat.cast_one, Nat.cast_ofNat] at _raw"
                            }
                        },
                    )
                }
                _ => {
                    return Err(LeanCompileError::unsupported(
                        "Matrix/CofactorExpansionOrder",
                    ));
                }
            };
            if proof.expression.ir() != expression.ir() {
                return Err(LeanCompileError::unsupported("Matrix/CofactorExpansion"));
            }
            let root = self.compile_object_reference(native, position)?;
            let checked = self.compile_verify(residual, position)?.1;
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(residual), usize::MAX);
            let expanded = self.compile_object_reference(&proof.expression, &formed)?;
            let orientation = if reversed { ".symm" } else { "" };
            return Ok(format!(
                "(by\n  let _cofactor := {root}\n  let _expanded := {expanded}\n  have _definition : Litex.Same _cofactor _expanded := by\n    have _raw := Litex.{name} (Litex.denote _cofactor.val.matrix){domain}{normalize}\n    exact _raw\n  exact (_definition.trans {checked}){orientation}\n)"
            ));
        }
        Err(LeanCompileError::unsupported(
            "Matrix/CofactorDefinitionSubject",
        ))
    }
}
