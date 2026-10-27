use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_matrix_operator_wd(
        &self,
        operator: &MatrixOperator,
        proof: &MatrixOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if matches!(
            operator,
            MatrixOperator::Add(_) | MatrixOperator::Subtract(_)
        ) {
            return self.compile_matrix_entrywise_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Scale(_)) {
            return self.compile_matrix_scale_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::OuterProduct(_)) {
            return self.compile_matrix_outer_wd(operator, proof, position);
        }
        if matches!(
            operator,
            MatrixOperator::EuclideanNorm(_) | MatrixOperator::FrobeniusNorm(_)
        ) {
            return self.compile_matrix_norm_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::InnerProduct(_)) {
            return self.compile_finite_inner_product_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Apply(_)) {
            return self.compile_matrix_apply_wd(operator, proof, position);
        }
        if matches!(
            operator,
            MatrixOperator::Minor(_) | MatrixOperator::Cofactor(_)
        ) {
            return self.compile_matrix_deleted_index_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Power(_)) {
            return self.compile_matrix_power_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Multiply(_)) {
            return self.compile_matrix_multiply_wd(operator, proof, position);
        }
        if matches!(
            operator,
            MatrixOperator::Trace(_) | MatrixOperator::Determinant(_)
        ) {
            return self.compile_matrix_square_scalar_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Rank(_)) {
            return self.compile_matrix_rank_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Inverse(_)) {
            return self.compile_matrix_inverse_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Adjugate(_)) {
            return self.compile_matrix_adjugate_wd(operator, proof, position);
        }
        if matches!(operator, MatrixOperator::Diagonal(_)) {
            return self.compile_matrix_diagonal_wd(operator, proof, position);
        }
        if let (
            MatrixOperator::IdentityMatrix(m),
            MatrixOperatorObjWellDefinedProofByDef::IdentityMatrix(p),
        ) = (operator, proof)
        {
            if p.child_obj_well_defined.len() != 1 || p.requirement_fact_verified.len() != 1 {
                return Err(LeanCompileError::unsupported("Matrix/IdentityWDStages"));
            }
            ensure_object(&m.order, &p.child_obj_well_defined[0])?;
            if !matches!(source_subject(&p.requirement_fact_verified[0])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==m.order.ir() && f.set==Obj::StandardSet(StandardSet::N))
            {
                return Err(LeanCompileError::unsupported("Matrix/IdentityOrder"));
            }
            let order = self.compile_wd(
                &p.child_obj_well_defined[0],
                &SourcePosition {
                    before: 0,
                    ..*position
                },
            )?;
            let member = self.compile_wd_requirement(
                &p.requirement_fact_verified[0],
                &SourcePosition {
                    before: 1,
                    ..*position
                },
            )?;
            return Ok(format!("(Litex.identityMatrix {order} {member})"));
        }
        let (constructor, objects, dimensions, input, children, requirements) =
            match (operator, proof) {
                (
                    MatrixOperator::ZeroMatrix(m),
                    MatrixOperatorObjWellDefinedProofByDef::ZeroMatrix(p),
                ) => (
                    "zeroMatrix",
                    vec![m.rows.as_ref(), m.cols.as_ref()],
                    [m.rows.as_ref(), m.cols.as_ref()],
                    None,
                    &p.child_obj_well_defined,
                    &p.requirement_fact_verified,
                ),
                (
                    MatrixOperator::Transpose(m),
                    MatrixOperatorObjWellDefinedProofByDef::Transpose(p),
                ) => (
                    "transpose",
                    vec![m.matrix.as_ref(), m.rows.as_ref(), m.cols.as_ref()],
                    [m.rows.as_ref(), m.cols.as_ref()],
                    Some(m.matrix.as_ref()),
                    &p.child_obj_well_defined,
                    &p.requirement_fact_verified,
                ),
                (
                    MatrixOperator::ConjugateTranspose(m),
                    MatrixOperatorObjWellDefinedProofByDef::ConjugateTranspose(p),
                ) => (
                    "conjugateTranspose",
                    vec![m.matrix.as_ref(), m.rows.as_ref(), m.cols.as_ref()],
                    [m.rows.as_ref(), m.cols.as_ref()],
                    Some(m.matrix.as_ref()),
                    &p.child_obj_well_defined,
                    &p.requirement_fact_verified,
                ),
                _ => return Err(LeanCompileError::unsupported("Matrix/OperatorWD")),
            };
        if children.len() != objects.len() || requirements.len() != 2 + usize::from(input.is_some())
        {
            return Err(LeanCompileError::unsupported("Matrix/OperatorWDStages"));
        }
        for (index, dimension) in dimensions.iter().enumerate() {
            if !matches!(source_subject(&requirements[index])?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == dimension.ir() && f.set == Obj::StandardSet(StandardSet::N))
            {
                return Err(LeanCompileError::unsupported("Matrix/OperatorDimension"));
            }
        }
        if let Some(input) = input {
            if !matches!(source_subject(&requirements[2])?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == input.ir() && matches!(&f.set,Obj::SetFormer(SetFormer::MatrixSet(m))
                    if m.set.as_ref() == &Obj::StandardSet(StandardSet::C) && m.rows.ir() == dimensions[0].ir() && m.cols.ir() == dimensions[1].ir()))
            {
                return Err(LeanCompileError::unsupported("Matrix/OperatorInput"));
            }
        }
        let mut arguments = Vec::new();
        for (index, object) in objects.iter().enumerate() {
            ensure_object(object, &children[index])?;
            arguments.push(self.compile_wd(
                &children[index],
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        for (index, requirement) in requirements.iter().enumerate() {
            arguments.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: children.len() + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.{constructor} {})", arguments.join(" ")))
    }
}
