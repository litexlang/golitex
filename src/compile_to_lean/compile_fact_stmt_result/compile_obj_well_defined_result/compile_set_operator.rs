use crate::compile_to_lean::helper::ensure_object;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::SetOperatorObjWellDefinedProofByDef;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_set_operator_wd(
        &self,
        object: &SetOperator,
        proof: &SetOperatorObjWellDefinedProofByDef,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (constructor, children, requirements, subjects): (_, _, _, Vec<&Obj>) =
            match (object, proof) {
                (SetOperator::Union(value), SetOperatorObjWellDefinedProofByDef::Union(wd)) => (
                    "union",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.left.as_ref(), value.right.as_ref()],
                ),
                (
                    SetOperator::PowerSet(value),
                    SetOperatorObjWellDefinedProofByDef::PowerSet(wd),
                ) => (
                    "powerSet",
                    &wd.child_obj_well_defined,
                    &wd.requirement_fact_verified,
                    vec![value.set.as_ref()],
                ),
                (SetOperator::Union(_) | SetOperator::PowerSet(_), _) => {
                    return Err(LeanCompileError::new(
                        "SetOperator/Constructor",
                        "Set operator evidence belongs to another source constructor.",
                    ))
                }
                _ => return Err(LeanCompileError::unsupported("WD/SetOperator")),
            };
        if children.len() != subjects.len() || !requirements.is_empty() {
            return Err(LeanCompileError::new(
                "SetOperator/Stages",
                "This set operator requires exactly its ordered child WD stages.",
            ));
        }
        let mut terms = Vec::with_capacity(subjects.len());
        for (index, (subject, child)) in subjects.iter().zip(children).enumerate() {
            ensure_object(subject, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        Ok(format!("(Litex.{constructor} {})", terms.join(" ")))
    }
}
