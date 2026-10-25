use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_subset_monotone(
        &self,
        fact: &SubsetFact,
        proof: &VerifyFactResult,
        power: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (left_base, right_base, law, args) = match (&fact.left, &fact.right) {
            (
                Obj::SetOperator(SetOperator::PowerSet(a)),
                Obj::SetOperator(SetOperator::PowerSet(b)),
            ) if power => (
                &a.set,
                &b.set,
                "powerSetMono",
                "_subset_left.val.bound _subset_right.val.bound",
            ),
            (
                Obj::SetOperator(SetOperator::SetMinus(a)),
                Obj::SetOperator(SetOperator::SetMinus(b)),
            ) if !power && a.right.ir() == b.right.ir() => (
                &a.left,
                &b.left,
                "setMinusMono",
                "_subset_left.val.left _subset_right.val.left _subset_left.val.right",
            ),
            _ => return Err(LeanCompileError::unsupported("SubsetMonotone/Constructors")),
        };
        if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::SubsetFact(p))
            if p.left.ir() == left_base.ir() && p.right.ir() == right_base.ir())
        {
            return Err(LeanCompileError::unsupported("SubsetMonotone/Premise"));
        }
        let child = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let left = self.compile_object_reference(&fact.left, &complete)?;
        let right = self.compile_object_reference(&fact.right, &complete)?;
        Ok(format!("(let _subset_left := {left}; let _subset_right := {right}; Litex.{law} {args} {child})"))
    }

    pub(super) fn compile_subset_transitivity(
        &self,
        fact: &SubsetFact,
        proofs: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Fact::AtomicFact(AtomicFact::SubsetFact(first)) = source_subject(proofs[0])? else {
            return Err(LeanCompileError::unsupported("SubsetTransitivity/First"));
        };
        let Fact::AtomicFact(AtomicFact::SubsetFact(second)) = source_subject(proofs[1])? else {
            return Err(LeanCompileError::unsupported("SubsetTransitivity/Second"));
        };
        if first.left.ir() != fact.left.ir()
            || first.right.ir() != second.left.ir()
            || second.right.ir() != fact.right.ir()
        {
            return Err(LeanCompileError::unsupported(
                "SubsetTransitivity/Endpoints",
            ));
        }
        let first_proof = self
            .compile_verify(proofs[0], &position.atomic_search_prior(0)?)?
            .1;
        let second_proof = self
            .compile_verify(proofs[1], &position.atomic_search_prior(1)?)?
            .1;
        let complete = position.atomic_search_prior(2)?;
        Ok(format!(
            "(Litex.subsetTrans {} {} {} {first_proof} {second_proof})",
            self.compile_object_reference(&fact.left, &complete)?,
            self.compile_object_reference(&first.right, &complete)?,
            self.compile_object_reference(&fact.right, &complete)?
        ))
    }

    pub(super) fn compile_union_upper_bound(
        &self,
        fact: &SubsetFact,
        proofs: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Union(set)) = &fact.left else {
            return Err(LeanCompileError::unsupported("UnionUpperBound/Carrier"));
        };
        let mut children = Vec::new();
        for (index, (proof, bound)) in proofs.into_iter().zip([&set.left, &set.right]).enumerate() {
            if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::SubsetFact(p))
                if p.left.ir() == bound.ir() && p.right.ir() == fact.right.ir())
            {
                return Err(LeanCompileError::unsupported("UnionUpperBound/Premise"));
            }
            children.push(
                self.compile_verify(proof, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        let union = self.compile_object_reference(&fact.left, &complete)?;
        let target = self.compile_object_reference(&fact.right, &complete)?;
        Ok(format!("(let _union := {union}; Litex.unionSubsetOfBoth _union.val.left _union.val.right {target} {} {})",children[0],children[1]))
    }

    pub(super) fn compile_union_upper_bound_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::SubsetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("UnionUpperBound/Family"));
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "UnionUpperBound/Requirements",
            ));
        }
        for (requirement, proof) in requirements.iter().zip(proofs) {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "UnionUpperBound/RequirementSubject",
                ));
            }
        }
        self.compile_union_upper_bound(fact, [&proofs[0], &proofs[1]], position)
    }

    pub(super) fn compile_set_minus_upper_bound_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::SubsetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("SetMinusUpperBound/Family"));
        };
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &fact.left else {
            return Err(LeanCompileError::unsupported("SetMinusUpperBound/Carrier"));
        };
        let ([requirement], [proof]) = (requirements, proofs) else {
            return Err(LeanCompileError::unsupported(
                "SetMinusUpperBound/Requirements",
            ));
        };
        if !matches!(requirement, Fact::AtomicFact(AtomicFact::SubsetFact(p))
            if p.left.ir() == set.left.ir() && p.right.ir() == fact.right.ir())
            || source_subject(proof)? != *requirement
        {
            return Err(LeanCompileError::unsupported(
                "SetMinusUpperBound/RequirementSubject",
            ));
        }
        let child = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let set = self.compile_object_reference(&fact.left, &complete)?;
        let target = self.compile_object_reference(&fact.right, &complete)?;
        Ok(format!("(let _set := {set}; Litex.setMinusSubsetOfLeft _set.val.left _set.val.right {target} {child})"))
    }
}
