use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_real_interval_member(
        &self,
        fact: &InFact,
        proofs: &[&VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (law, bounds) = match &fact.set {
            Obj::SetFormer(SetFormer::IntervalObj(p)) => {
                let (a, b, lc, rc) = real_interval_parts(p);
                (
                    "inRealInterval_iff",
                    vec![(a, &fact.element, lc), (&fact.element, b, rc)],
                )
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => {
                let (a, lower, closed) = real_ray_parts(p);
                (
                    "inRealRay_iff",
                    vec![if lower {
                        (a, &fact.element, closed)
                    } else {
                        (&fact.element, a, closed)
                    }],
                )
            }
            _ => return Err(LeanCompileError::unsupported("RealInterval/MemberSubject")),
        };
        if proofs.len() != bounds.len() + 1 {
            return Err(LeanCompileError::unsupported("RealInterval/MemberStages"));
        }
        if !matches!(source_subject(proofs[0])?,Fact::AtomicFact(AtomicFact::InFact(f)) if f.element.ir()==fact.element.ir() && f.set==Obj::StandardSet(StandardSet::R))
        {
            return Err(LeanCompileError::unsupported("RealInterval/MemberCarrier"));
        }
        for ((a, b, closed), proof) in bounds.iter().zip(&proofs[1..]) {
            if !real_bound_subject(&source_subject(proof)?, a, b, *closed) {
                return Err(LeanCompileError::unsupported("RealInterval/MemberBound"));
            }
        }
        let checked = proofs
            .iter()
            .map(|p| self.compile_verify(p, position).map(|p| p.1))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!(
            "((Litex.{law} {} {}).mpr ⟨{}⟩)",
            self.compile_object_reference(&fact.set, position)?,
            self.compile_object_reference(&fact.element, position)?,
            checked.join(", ")
        ))
    }

    pub(in crate::compile_to_lean) fn compile_real_interval_nonmember(
        &self,
        fact: &NotInFact,
        proof: &VerifyFactResult,
        endpoint: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let subject = source_subject(proof)?;
        let equal_to = |a: &Obj| matches!(&subject,Fact::AtomicFact(AtomicFact::EqualFact(f)) if f.left.ir()==fact.element.ir() && f.right.ir()==a.ir());
        let law = match &fact.set {
            Obj::SetFormer(SetFormer::IntervalObj(p)) => {
                let (a, b, lc, rc) = real_interval_parts(p);
                if endpoint && !lc && equal_to(a) {
                    "notInRealIntervalOpenLower"
                } else if endpoint && !rc && equal_to(b) {
                    "notInRealIntervalOpenUpper"
                } else if !endpoint && real_bound_subject(&subject, &fact.element, a, false) {
                    "notInRealIntervalLower"
                } else if !endpoint && real_bound_subject(&subject, b, &fact.element, false) {
                    "notInRealIntervalUpper"
                } else {
                    return Err(LeanCompileError::unsupported(
                        "RealInterval/NonmemberPremise",
                    ));
                }
            }
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(p)) => {
                let (a, lower, closed) = real_ray_parts(p);
                let (l, r) = if lower {
                    (&fact.element, a)
                } else {
                    (a, &fact.element)
                };
                if endpoint && !closed && equal_to(a) {
                    "notInRealRayEndpoint"
                } else if !endpoint && real_bound_subject(&subject, l, r, !closed) {
                    "notInRealRayOpposite"
                } else {
                    return Err(LeanCompileError::unsupported("RealRay/NonmemberPremise"));
                }
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "RealInterval/NonmemberSubject",
                ))
            }
        };
        let proof = self.compile_verify(proof, position)?.1;
        Ok(format!(
            "(Litex.{law} {} {} {proof})",
            self.compile_object_reference(&fact.set, position)?,
            self.compile_object_reference(&fact.element, position)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_real_interval_subset(
        &self,
        fact: &SubsetFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        if fact.right != Obj::StandardSet(StandardSet::R) {
            return Err(LeanCompileError::unsupported("RealInterval/SubsetTarget"));
        }
        let law = match &fact.left {
            Obj::SetFormer(SetFormer::IntervalObj(_)) => "realIntervalSubsetR",
            Obj::SetFormer(SetFormer::OneSideInfinityIntervalObj(_)) => "realRaySubsetR",
            _ => return Err(LeanCompileError::unsupported("RealInterval/SubsetSource")),
        };
        Ok(format!(
            "(Litex.{law} {})",
            self.compile_object_reference(&fact.left, position)?
        ))
    }
}
