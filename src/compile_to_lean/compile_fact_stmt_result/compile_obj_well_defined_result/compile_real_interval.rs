use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::well_defined_results::verify_obj::{
    IntervalObjObjWellDefinedProof, OneSideInfinityIntervalObjObjWellDefinedProof,
};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_interval_wd(
        &self,
        source: &IntervalObj,
        proof: &IntervalObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (a, b, lc, rc) = real_interval_parts(source);
        let args = self.compile_real_endpoint_wd(
            &[a, b],
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
            position,
        )?;
        Ok(format!("(Litex.realInterval {lc} {rc} {})", args.join(" ")))
    }

    pub(in crate::compile_to_lean) fn compile_real_ray_wd(
        &self,
        source: &OneSideInfinityIntervalObj,
        proof: &OneSideInfinityIntervalObjObjWellDefinedProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (a, lower, closed) = real_ray_parts(source);
        let args = self.compile_real_endpoint_wd(
            &[a],
            &proof.child_obj_well_defined,
            &proof.requirement_fact_verified,
            position,
        )?;
        Ok(format!(
            "(Litex.realRay {lower} {closed} {})",
            args.join(" ")
        ))
    }

    fn compile_real_endpoint_wd(
        &self,
        endpoints: &[&Obj],
        children: &[Box<ObjWellDefinedProof>],
        requirements: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        if children.len() != endpoints.len() || requirements.len() != endpoints.len() {
            return Err(LeanCompileError::unsupported("RealInterval/WDStages"));
        }
        let mut args = Vec::new();
        for (i, endpoint) in endpoints.iter().enumerate() {
            ensure_object(endpoint, &children[i])?;
            if !matches!(source_subject(&requirements[i])?, Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==endpoint.ir() && f.set==Obj::StandardSet(StandardSet::R))
            {
                return Err(LeanCompileError::unsupported(
                    "RealInterval/EndpointMembership",
                ));
            }
            args.push(self.compile_wd(
                &children[i],
                &SourcePosition {
                    before: i,
                    ..*position
                },
            )?);
        }
        for (i, requirement) in requirements.iter().enumerate() {
            args.push(self.compile_wd_requirement(
                requirement,
                &SourcePosition {
                    before: endpoints.len() + i,
                    ..*position
                },
            )?);
        }
        Ok(args)
    }
}
