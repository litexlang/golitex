//! Replay the finite inner product with conjugation on the left operand.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::matrix_operations::{
    FiniteInnerProductScalarProof, MatrixRealOperandProof, MatrixScalarCarrierProof,
};
use crate::execute::execute_fact_stmt::native_matrix::{
    matrix_call, matrix_identifier, MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;
impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_inner_product_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (
            MatrixOperator::InnerProduct(m),
            MatrixOperatorObjWellDefinedProofByDef::InnerProduct(p),
        ) = (operator, proof)
        else {
            return Err(LeanCompileError::unsupported("Matrix/InnerProductWD"));
        };
        if p.child_obj_well_defined.len() != 3 || p.requirement_fact_verified.len() != 3 {
            return Err(LeanCompileError::unsupported("Matrix/InnerProductWDStages"));
        }
        for (index, subject) in [&m.dimension, &m.left, &m.right].iter().enumerate() {
            let expected = if index == 0 {
                Obj::StandardSet(StandardSet::N)
            } else {
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: m.dimension.clone(),
                }))
            };
            if !matches!(source_subject(&p.requirement_fact_verified[index])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==subject.ir() && f.set.ir()==expected.ir())
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/InnerProductWDPremise",
                ));
            }
        }
        let mut args = Vec::new();
        for (index, subject) in [&m.left, &m.right, &m.dimension].iter().enumerate() {
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
        Ok(format!("(Litex.finiteInnerProduct {})", args.join(" ")))
    }
    pub(in crate::compile_to_lean) fn compile_finite_inner_product_member(
        &self,
        fact: &InFact,
        proof: &FiniteInnerProductScalarProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::MatrixOperator(MatrixOperator::InnerProduct(m)) = &fact.element else {
            return Err(LeanCompileError::unsupported("Matrix/InnerProductSubject"));
        };
        let root = self.compile_object_reference(&fact.element, position)?;
        match &proof.carrier {
            MatrixScalarCarrierProof::StandardSubset
                if fact.set == Obj::StandardSet(StandardSet::C) =>
            {
                Ok(format!("(Litex.finiteInnerProductInC {root})"))
            }
            MatrixScalarCarrierProof::RealInputs(operands)
                if operands.len() == 2 && fact.set == Obj::StandardSet(StandardSet::R) =>
            {
                let mut args = Vec::new();
                for (operand, source) in operands.iter().zip([&m.left, &m.right]) {
                    let MatrixRealOperandProof::Membership(checked) = operand else {
                        return Err(LeanCompileError::unsupported("Matrix/InnerProductRealRule"));
                    };
                    let Fact::AtomicFact(AtomicFact::InFact(f)) = source_subject(checked)? else {
                        return Err(LeanCompileError::unsupported(
                            "Matrix/InnerProductRealSubject",
                        ));
                    };
                    let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &f.set else {
                        return Err(LeanCompileError::unsupported(
                            "Matrix/InnerProductRealSignature",
                        ));
                    };
                    if f.element.ir() != source.ir() {
                        return Err(LeanCompileError::unsupported(
                            "Matrix/InnerProductRealOperand",
                        ));
                    }
                    Self::validate_finite_seq_signature(
                        &FiniteSeqSet {
                            set: Box::new(Obj::StandardSet(StandardSet::R)),
                            n: m.dimension.clone(),
                        },
                        signature,
                    )?;
                    args.push(self.compile_verify(checked, position)?.1);
                }
                Ok(format!(
                    "(Litex.finiteInnerProductInR {root} {})",
                    args.join(" ")
                ))
            }
            _ => Err(LeanCompileError::unsupported("Matrix/InnerProductCarrier")),
        }
    }
    pub(in crate::compile_to_lean) fn compile_finite_inner_product_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixScalarDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let MatrixDefinitionResidualProof::Verified(residual) = proof.equality.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/InnerProductResidual"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported(
                "Matrix/InnerProductResidualSubject",
            ));
        };
        if equal.left.ir() != proof.expression.ir() {
            return Err(LeanCompileError::unsupported(
                "Matrix/InnerProductResidualEndpoint",
            ));
        }
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let Obj::MatrixOperator(MatrixOperator::InnerProduct(m)) = native else {
                continue;
            };
            if equal.right.ir() != other.ir() {
                continue;
            }
            let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = &proof.expression
            else {
                return Err(LeanCompileError::unsupported("Matrix/InnerProductSum"));
            };
            if !matches!(sum.set.as_ref(),Obj::SetFormer(SetFormer::ClosedRange(r)) if closed_integer(&r.start)==Some(1) && r.end.ir()==m.dimension.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/InnerProductIndices"));
            }
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
                return Err(LeanCompileError::unsupported("Matrix/InnerProductIterand"));
            };
            let groups = &f.body.set_bound_parameters.groups;
            if groups.len() != 1
                || groups[0].params.len() != 1
                || groups[0].param_type.ir() != sum.set.ir()
                || !f.body.dom_facts.is_empty()
                || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::C)
            {
                return Err(LeanCompileError::unsupported(
                    "Matrix/InnerProductIterandSignature",
                ));
            }
            let k = matrix_identifier(&groups[0].params[0]);
            let expected = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                left: Box::new(Obj::ComplexOperator(ComplexOperator::Conjugate(
                    Conjugate {
                        arg: Box::new(matrix_call(&m.left, vec![k.clone()])),
                    },
                ))),
                right: Box::new(matrix_call(&m.right, vec![k])),
            }));
            if f.equal_to.ir() != expected.ir() {
                return Err(LeanCompileError::unsupported(
                    "Matrix/InnerProductIterandBody",
                ));
            }
            let root = self.compile_object_reference(native, position)?;
            let checked = self.compile_verify(residual, position)?.1;
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(residual), usize::MAX);
            let expanded = self.compile_object_reference(&proof.expression, &formed)?;
            let bridge = format!(
                "(show Litex.Same {root} {expanded} from Litex.finiteInnerProductFormula {root} ({expanded}).val.function (by rfl) (by rfl))"
            );
            let result = format!("({bridge}.trans {checked})");
            return Ok(if reversed {
                format!("({result}).symm")
            } else {
                result
            });
        }
        Err(LeanCompileError::unsupported(
            "Matrix/InnerProductDefinitionSubject",
        ))
    }
}
