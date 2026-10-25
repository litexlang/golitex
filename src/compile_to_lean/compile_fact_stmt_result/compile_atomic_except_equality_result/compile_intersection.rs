use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_intersection_membership_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("Intersection/MemberFamily"));
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "Intersection/MemberRequirements",
            ));
        }
        for (requirement, proof) in requirements.iter().zip(proofs) {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported(
                    "Intersection/RequirementSubject",
                ));
            }
        }
        self.compile_intersection_membership(fact, [&proofs[0], &proofs[1]], position)
    }

    pub(super) fn compile_intersection_membership(
        &self,
        fact: &InFact,
        proofs: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Intersect(set)) = &fact.set else {
            return Err(LeanCompileError::unsupported("Intersection/Carrier"));
        };
        let mut terms = Vec::new();
        for (i, (proof, bound)) in proofs.into_iter().zip([&set.left, &set.right]).enumerate() {
            if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::InFact(p))
                if p.element.ir() == fact.element.ir() && p.set.ir() == bound.ir())
            {
                return Err(LeanCompileError::unsupported("Intersection/ChildSubject"));
            }
            terms.push(
                self.compile_verify(proof, &position.atomic_search_prior(i)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        Ok(format!(
            "((Litex.inIntersect_iff {} {} {}).mpr ⟨{}, {}⟩)",
            self.compile_object_reference(&fact.element, &complete)?,
            self.compile_object_reference(&set.left, &complete)?,
            self.compile_object_reference(&set.right, &complete)?,
            terms[0],
            terms[1]
        ))
    }

    pub(super) fn compile_intersection_subset_operand(
        &self,
        fact: &SubsetFact,
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Intersect(set)) = &fact.left else {
            return Err(LeanCompileError::unsupported("Intersection/SubsetSource"));
        };
        let operand = if left { &set.left } else { &set.right };
        if operand.ir() != fact.right.ir() {
            return Err(LeanCompileError::unsupported("Intersection/SubsetOperand"));
        }
        let law = if left {
            "intersectSubsetLeft"
        } else {
            "intersectSubsetRight"
        };
        Ok(format!(
            "(Litex.{law} {} {})",
            self.compile_object_reference(&set.left, position)?,
            self.compile_object_reference(&set.right, position)?
        ))
    }

    pub(super) fn compile_intersection_subset_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::SubsetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("Intersection/SubsetFamily"));
        };
        let ([requirement], [proof]) = (requirements, proofs) else {
            return Err(LeanCompileError::unsupported(
                "Intersection/UpperBoundRequirements",
            ));
        };
        if source_subject(proof)? != *requirement {
            return Err(LeanCompileError::unsupported(
                "Intersection/UpperBoundRequirementSubject",
            ));
        }
        self.compile_intersection_subset_bound(fact, proof, left, position)
    }

    pub(super) fn compile_intersection_subset_bound(
        &self,
        fact: &SubsetFact,
        proof: &VerifyFactResult,
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Intersect(set)) = &fact.left else {
            return Err(LeanCompileError::unsupported("Intersection/SubsetSource"));
        };
        let operand = if left { &set.left } else { &set.right };
        if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::SubsetFact(p))
            if p.left.ir() == operand.ir() && p.right.ir() == fact.right.ir())
        {
            return Err(LeanCompileError::unsupported(
                "Intersection/SubsetBoundSubject",
            ));
        }
        let term = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let law = if left {
            "intersectSubsetOfLeft"
        } else {
            "intersectSubsetOfRight"
        };
        Ok(format!(
            "(Litex.{law} {} {} {} {term})",
            self.compile_object_reference(&set.left, &complete)?,
            self.compile_object_reference(&set.right, &complete)?,
            self.compile_object_reference(&fact.right, &complete)?
        ))
    }

    pub(super) fn compile_subset_into_intersection(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::SubsetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("Intersection/SubsetFamily"));
        };
        let Obj::SetOperator(SetOperator::Intersect(set)) = &fact.right else {
            return Err(LeanCompileError::unsupported("Intersection/SubsetTarget"));
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::unsupported(
                "Intersection/SubsetRequirements",
            ));
        }
        let mut terms = Vec::new();
        for (i, bound) in [&set.left, &set.right].into_iter().enumerate() {
            if !matches!(&requirements[i], Fact::AtomicFact(AtomicFact::SubsetFact(p))
                if p.left.ir() == fact.left.ir() && p.right.ir() == bound.ir())
                || source_subject(&proofs[i])? != requirements[i]
            {
                return Err(LeanCompileError::unsupported(
                    "Intersection/SubsetChildSubject",
                ));
            }
            terms.push(
                self.compile_verify(&proofs[i], &position.atomic_search_prior(i)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        Ok(format!(
            "(Litex.subsetIntersect {} {} {} {} {})",
            self.compile_object_reference(&fact.left, &complete)?,
            self.compile_object_reference(&set.left, &complete)?,
            self.compile_object_reference(&set.right, &complete)?,
            terms[0],
            terms[1]
        ))
    }
}
