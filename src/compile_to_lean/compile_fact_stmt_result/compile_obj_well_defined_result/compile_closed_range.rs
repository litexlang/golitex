use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::ClosedRangeObjWellDefinedProof;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_closed_range_wd(
        &self,
        range: &ClosedRange,
        proof: &ClosedRangeObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if proof.child_obj_well_defined.len() != 2 || proof.requirement_fact_verified.len() != 2 {
            return Err(LeanCompileError::new(
                "ClosedRange/Stages",
                "A closed integer range needs its two endpoint WD and integer-membership stages.",
            ));
        }
        let endpoints = [&range.start, &range.end];
        let mut terms = Vec::new();
        for (index, endpoint) in endpoints.iter().enumerate() {
            let child = &proof.child_obj_well_defined[index];
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
            let evidence = &proof.requirement_fact_verified[index];
            if !matches!(source_subject(evidence)?, Fact::AtomicFact(AtomicFact::InFact(f))
                if f.element.ir() == endpoint.ir() && f.set == Obj::StandardSet(StandardSet::Z))
            {
                return Err(LeanCompileError::new(
                    "ClosedRange/Endpoint",
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
            "(Litex.closedRange {} {} {} {})",
            terms[0], terms[1], members[0], members[1]
        ))
    }
}
