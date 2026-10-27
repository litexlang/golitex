//! Replay finite vector and matrix norms with their original ordered WD proofs.
use super::helper::*;
use super::source_position::{SourceOwner, SourcePosition};
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::native_matrix::{
    MatrixDefinitionResidualProof, MatrixScalarDefinitionProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

pub(super) fn validate_norm_sum(native: &Obj, sum: &Obj) -> Result<(), LeanCompileError> {
    use crate::execute::execute_fact_stmt::matrix_operations::{modulus, pow};
    use crate::execute::execute_fact_stmt::native_matrix::{
        matrix_call, matrix_identifier, matrix_number,
    };
    let (operand, rows, cols) = match native {
        Obj::MatrixOperator(MatrixOperator::EuclideanNorm(p)) => {
            (p.vector.as_ref(), p.dimension.as_ref(), None)
        }
        Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(p)) => {
            (p.matrix.as_ref(), p.rows.as_ref(), Some(p.cols.as_ref()))
        }
        _ => return Err(LeanCompileError::unsupported("Matrix/NormSumSubject")),
    };
    let (function, row) = norm_sum_iterand(sum, rows)?;
    let (body, arguments) = if let Some(cols) = cols {
        let (inner, col) = norm_sum_iterand(&function.equal_to, cols)?;
        (
            inner.equal_to.as_ref(),
            vec![matrix_identifier(row), matrix_identifier(col)],
        )
    } else {
        (function.equal_to.as_ref(), vec![matrix_identifier(row)])
    };
    let expected = pow(modulus(matrix_call(operand, arguments)), matrix_number(2));
    if body.ir() != expected.ir() {
        return Err(LeanCompileError::unsupported("Matrix/NormSumBody"));
    }
    Ok(())
}

fn norm_sum_iterand<'a>(
    sum: &'a Obj,
    dimension: &Obj,
) -> Result<(&'a AnonymousFn, &'a BoundName), LeanCompileError> {
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = sum else {
        return Err(LeanCompileError::unsupported("Matrix/NormFiniteSum"));
    };
    if !matches!(sum.set.as_ref(), Obj::SetFormer(SetFormer::ClosedRange(r))
        if closed_integer(&r.start) == Some(1) && r.end.ir() == dimension.ir())
    {
        return Err(LeanCompileError::unsupported("Matrix/NormSumIndices"));
    }
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = sum.func.as_ref() else {
        return Err(LeanCompileError::unsupported("Matrix/NormIterand"));
    };
    let groups = &f.body.set_bound_parameters.groups;
    if groups.len() != 1
        || groups[0].params.len() != 1
        || groups[0].param_type.ir() != sum.set.ir()
        || !f.body.dom_facts.is_empty()
        || f.body.ret_set.as_ref() != &Obj::StandardSet(StandardSet::R)
    {
        return Err(LeanCompileError::unsupported("Matrix/NormIterandSignature"));
    }
    Ok((f, &groups[0].params[0]))
}

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_norm_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (name, objects, dimensions, carrier, children, requirements) = match (operator, proof) {
            (
                MatrixOperator::EuclideanNorm(m),
                MatrixOperatorObjWellDefinedProofByDef::EuclideanNorm(p),
            ) => (
                "euclideanNorm",
                vec![m.vector.as_ref(), m.dimension.as_ref()],
                vec![m.dimension.as_ref()],
                Obj::SetFormer(SetFormer::FiniteSeqSet(FiniteSeqSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    n: m.dimension.clone(),
                })),
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            (
                MatrixOperator::FrobeniusNorm(m),
                MatrixOperatorObjWellDefinedProofByDef::FrobeniusNorm(p),
            ) => (
                "frobeniusNorm",
                vec![m.matrix.as_ref(), m.rows.as_ref(), m.cols.as_ref()],
                vec![m.rows.as_ref(), m.cols.as_ref()],
                Obj::SetFormer(SetFormer::MatrixSet(MatrixSet {
                    set: Box::new(Obj::StandardSet(StandardSet::C)),
                    rows: m.rows.clone(),
                    cols: m.cols.clone(),
                })),
                &p.child_obj_well_defined,
                &p.requirement_fact_verified,
            ),
            _ => return Err(LeanCompileError::unsupported("Matrix/NormWD")),
        };
        if children.len() != objects.len() || requirements.len() != dimensions.len() + 1 {
            return Err(LeanCompileError::unsupported("Matrix/NormWDStages"));
        }
        for (index, dimension) in dimensions.iter().enumerate() {
            if !matches!(source_subject(&requirements[index])?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == dimension.ir() && f.set == Obj::StandardSet(StandardSet::N))
            {
                return Err(LeanCompileError::unsupported("Matrix/NormDimension"));
            }
        }
        if !matches!(source_subject(&requirements[dimensions.len()])?, Fact::AtomicFact(AtomicFact::InFact(f))
            if f.element.ir() == objects[0].ir() && f.set.ir() == carrier.ir())
        {
            return Err(LeanCompileError::unsupported("Matrix/NormOperand"));
        }
        let mut args = Vec::new();
        for (index, (subject, child)) in objects.iter().zip(children).enumerate() {
            ensure_object(subject, child)?;
            args.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, requirement) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: children.len() + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.{name} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_matrix_norm_member(
        &self,
        fact: &InFact,
        target: &StandardSet,
        euclidean: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let name = match &fact.element {
            Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_)) if euclidean => {
                "euclideanNormInR"
            }
            Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(_)) if !euclidean => {
                "frobeniusNormInR"
            }
            _ => return Err(LeanCompileError::unsupported("Matrix/NormMemberSubject")),
        };
        if fact.set != Obj::StandardSet(target.clone()) {
            return Err(LeanCompileError::unsupported("Matrix/NormMemberTarget"));
        }
        let root = self.compile_object_reference(&fact.element, position)?;
        standard_inclusion_term(
            &StandardSet::R,
            target,
            &root,
            &format!("(Litex.{name} {root})"),
        )
    }

    pub(in crate::compile_to_lean) fn compile_matrix_norm_definition(
        &self,
        fact: &EqualFact,
        proof: &MatrixScalarDefinitionProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let MatrixDefinitionResidualProof::Verified(residual) = proof.equality.as_ref() else {
            return Err(LeanCompileError::unsupported("Matrix/NormResidual"));
        };
        let Fact::AtomicFact(AtomicFact::EqualFact(equal)) = source_subject(residual)? else {
            return Err(LeanCompileError::unsupported("Matrix/NormResidualSubject"));
        };
        if equal.left.ir() != proof.expression.ir() {
            return Err(LeanCompileError::unsupported("Matrix/NormResidualEndpoint"));
        }
        let Obj::ExpLogOperator(ExpLogOperator::Sqrt(expression)) = &proof.expression else {
            return Err(LeanCompileError::unsupported("Matrix/NormSquareRoot"));
        };
        for (native, other, reversed) in [
            (&fact.left, &fact.right, false),
            (&fact.right, &fact.left, true),
        ] {
            let name = match native {
                Obj::MatrixOperator(MatrixOperator::EuclideanNorm(_)) => "euclideanNormFormula",
                Obj::MatrixOperator(MatrixOperator::FrobeniusNorm(_)) => "frobeniusNormFormula",
                _ => continue,
            };
            if equal.right.ir() != other.ir() {
                continue;
            }
            validate_norm_sum(native, &expression.arg)?;
            let root = self.compile_object_reference(native, position)?;
            let checked = self.compile_verify(residual, position)?.1;
            let formed =
                SourcePosition::new(Some(position), SourceOwner::Verify(residual), usize::MAX);
            let expanded = self.compile_object_reference(&proof.expression, &formed)?;
            // Bind the checked expansion once; its nested function WD can be large.
            let orientation = if reversed { ".symm" } else { "" };
            return Ok(format!("(by\n  let _norm := {root}\n  let _expanded := {expanded}\n  have _definition : Litex.Same _norm _expanded := Litex.{name} _norm (_expanded.val.arg).val.function (by rfl) (by rfl)\n  exact (_definition.trans {checked}){orientation}\n)"));
        }
        Err(LeanCompileError::unsupported(
            "Matrix/NormDefinitionSubject",
        ))
    }
}
