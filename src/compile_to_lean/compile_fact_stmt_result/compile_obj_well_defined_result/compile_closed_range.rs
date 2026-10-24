use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    ClosedRangeObjWellDefinedProof, RangeObjWellDefinedProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_range_wd(
        &self,
        range: &ClosedRange,
        proof: &ClosedRangeObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_integer_interval_wd(
            &range.start,
            &range.end,
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
            "closedRange",
            "ClosedRange",
            position,
        )
    }

    pub(in crate::compile_to_lean) fn compile_range_wd(
        &self,
        range: &Range,
        proof: &RangeObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_integer_interval_wd(
            &range.start,
            &range.end,
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
            "range",
            "Range",
            position,
        )
    }

    fn compile_integer_interval_wd(
        &self,
        start: &Obj,
        end: &Obj,
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        constructor: &str,
        family: &str,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if children.len() != 2 || requirements.len() != 2 {
            return Err(LeanCompileError::new(
                &format!("{family}/Stages"),
                "An integer range needs its two endpoint WD and integer-membership stages.",
            ));
        }
        let endpoints = [start, end];
        let mut terms = Vec::new();
        for (index, endpoint) in endpoints.iter().enumerate() {
            let child = &children[index];
            ensure_object(endpoint, child)?;
            terms.push(self.compile_wd(
                child,
                &SourcePosition {
                    before: index,
                    ..*position
                },
            )?);
        }
        let mut members = Vec::new();
        for (index, endpoint) in endpoints.iter().enumerate() {
            let evidence = &requirements[index];
            if !matches!(source_subject(evidence)?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == endpoint.ir() && f.set == Obj::StandardSet(StandardSet::Z))
            {
                return Err(LeanCompileError::new(
                    &format!("{family}/Endpoint"),
                    "The range requirement must establish this ordered endpoint in Z.",
                ));
            }
            members.push(
                self.compile_verify(
                    evidence,
                    &SourcePosition {
                        before: 2 + index,
                        ..*position
                    },
                )?
                .1,
            );
        }
        Ok(format!(
            "(Litex.{constructor} {} {} {} {})",
            terms[0], terms[1], members[0], members[1]
        ))
    }
}
