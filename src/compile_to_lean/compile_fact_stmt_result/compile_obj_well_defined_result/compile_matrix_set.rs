use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::MatrixSetObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn validate_matrix_signature(
        matrix: &MatrixSet,
        signature: &FnSet,
    ) -> Result<(), LeanCompileError> {
        let groups = &signature.set_bound_parameters.groups;
        if groups.len() != 2
            || !signature.dom_facts.is_empty()
            || signature.ret_set.ir() != matrix.set.ir()
        {
            return Err(LeanCompileError::unsupported("Matrix/Signature"));
        }
        for (group, dimension) in groups.iter().zip([&matrix.rows, &matrix.cols]) {
            if group.params.len() != 1
                || !matches!(group.param_type.as_ref(),
                Obj::SetFormer(SetFormer::ClosedRange(range))
                if matches!(range.start.as_ref(), Obj::Literal(Literal::Number(n)) if n.normalized_value == "1")
                    && range.end.ir() == dimension.ir())
            {
                return Err(LeanCompileError::unsupported("Matrix/Signature"));
            }
        }
        if groups[0].params[0].id == groups[1].params[0].id {
            return Err(LeanCompileError::unsupported("Matrix/RepeatedParameter"));
        }
        Ok(())
    }

    pub(in crate::compile_to_lean) fn compile_matrix_set_wd(
        &self,
        matrix: &MatrixSet,
        proof: &MatrixSetObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.child_obj_well_defined.len() != 3 || proof.requirement_fact_verified.len() != 3 {
            return Err(LeanCompileError::unsupported("Matrix/WDStages"));
        }
        let mut arguments = Vec::new();
        for (index, object) in [&matrix.set, &matrix.rows, &matrix.cols].iter().enumerate() {
            let wd = &proof.child_obj_well_defined[index];
            ensure_object(object, wd)?;
            arguments.push(self.compile_wd(
                wd,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
            let fact = source_subject(&proof.requirement_fact_verified[index])?;
            let matches = if index == 0 {
                matches!(fact, Fact::AtomicFact(AtomicFact::IsSetFact(f)) if f.set.ir() == object.ir())
            } else {
                matches!(fact, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir() == object.ir()
                    && f.set == Obj::StandardSet(StandardSet::N))
            };
            if !matches {
                return Err(LeanCompileError::unsupported("Matrix/WDRequirements"));
            }
        }
        for (index, requirement) in proof.requirement_fact_verified.iter().enumerate() {
            arguments.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: 3 + index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.matrixSet {})", arguments.join(" ")))
    }
}
