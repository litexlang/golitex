//! Pointwise continuity retains the original complete real domain and point membership.
use super::helper::*;
use super::source_position::SourcePosition;
use super::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::well_defined_result::{
    FunctionAnalysisPredicateDomainProof, PredicateDomainRequirementProof,
};
use crate::prelude::*;

pub(super) fn continuity_parts(fact: &AtomicFact) -> Option<(&Obj, &Obj, RealApproachSide, bool)> {
    Some(match fact {
        AtomicFact::FunctionContinuousAtFact(f) => (&f.function, &f.point, f.side, false),
        AtomicFact::NotFunctionContinuousAtFact(f) => (&f.function, &f.point, f.side, true),
        _ => return None,
    })
}
pub(super) fn continuity_side(side: RealApproachSide) -> &'static str {
    match side {
        RealApproachSide::Both => "both",
        RealApproachSide::Left => "left",
        RealApproachSide::Right => "right",
    }
}
impl LitexToLeanCompiler {
    pub(super) fn compile_function_continuity_domain(
        &self,
        fact: &AtomicFact,
        proof: &FunctionAnalysisPredicateDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<Vec<String>, LeanCompileError> {
        let (function, point, _, _) = continuity_parts(fact)
            .ok_or_else(|| LeanCompileError::unsupported("Continuity/PredicateFamily"))?;
        let [requirement] = proof.requirements.as_slice() else {
            return Err(LeanCompileError::unsupported(
                "Continuity/PointRequirements",
            ));
        };
        if !matches!(&requirement.requirement,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==point.ir()&&f.set.ir()==proof.function_domain.domain.ir())
        {
            return Err(LeanCompileError::unsupported("Continuity/PointDomain"));
        }
        let domain =
            self.compile_real_function_domain(function, &proof.function_domain, position)?;
        let function_term = self.compile_object_reference(function, position)?;
        let args = atomic_fact_args_ref(fact);
        let prior = SourcePosition {
            before: args.len(),
            ..*position
        };
        let (ty, term) = match &requirement.result {
            PredicateDomainRequirementProof::Verified(p) => {
                if source_subject(p)? != requirement.requirement {
                    return Err(LeanCompileError::unsupported("Continuity/PointEvidence"));
                }
                self.compile_verify(p, &prior)?
            }
            PredicateDomainRequirementProof::CheckedArgument(p) => (
                self.compile_function_raw_predicate(
                    &requirement.requirement,
                    &prior,
                    &std::collections::HashMap::new(),
                )?,
                self.compile_checked_domain_argument(
                    &requirement.requirement,
                    p,
                    &args,
                    0,
                    &prior,
                )?,
            ),
        };
        Ok(vec![
   format!("have _continuity_domain : Litex.RealFunctionValue M (Litex.denote {function_term}) := {domain}"),
   format!("have h_{} : {ty} := {term}",requirement.requirement.fact_id().value()),
  ])
    }
}
