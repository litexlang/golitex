use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_set_minus_membership_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("SetMinus/MemberFamily"));
        };
        if requirements.len() != 2 || proofs.len() != 2 {
            return Err(LeanCompileError::unsupported("SetMinus/MemberRequirements"));
        }
        for (requirement, proof) in requirements.iter().zip(proofs) {
            if source_subject(proof)? != *requirement {
                return Err(LeanCompileError::unsupported("SetMinus/RequirementSubject"));
            }
        }
        self.compile_set_minus_membership(fact, [&proofs[0], &proofs[1]], position)
    }

    pub(super) fn compile_set_minus_membership(
        &self,
        fact: &InFact,
        proofs: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &fact.set else {
            return Err(LeanCompileError::unsupported("SetMinus/Carrier"));
        };
        if !matches!(source_subject(proofs[0])?, Fact::AtomicFact(AtomicFact::InFact(p))
            if p.element.ir() == fact.element.ir() && p.set.ir() == set.left.ir())
            || !matches!(source_subject(proofs[1])?, Fact::AtomicFact(AtomicFact::NotInFact(p))
                if p.element.ir() == fact.element.ir() && p.set.ir() == set.right.ir())
        {
            return Err(LeanCompileError::unsupported("SetMinus/ChildSubject"));
        }
        let left = self
            .compile_verify(proofs[0], &position.atomic_search_prior(0)?)?
            .1;
        let right = self
            .compile_verify(proofs[1], &position.atomic_search_prior(1)?)?
            .1;
        let complete = position.atomic_search_prior(2)?;
        let set = self.compile_object_reference(&fact.set, &complete)?;
        let element = self.compile_object_reference(&fact.element, &complete)?;
        Ok(format!("(let _set := {set}; (Litex.inSetMinus_iff {element} _set.val.left _set.val.right).mpr ⟨{left}, {right}⟩)"))
    }

    pub(super) fn compile_set_minus_nonmembership(
        &self,
        fact: &NotInFact,
        proof: &VerifyFactResult,
        right: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &fact.set else {
            return Err(LeanCompileError::unsupported("SetMinus/NegativeCarrier"));
        };
        let subject = source_subject(proof)?;
        let matches = if right {
            matches!(subject, Fact::AtomicFact(AtomicFact::InFact(p))
                if p.element.ir() == fact.element.ir() && p.set.ir() == set.right.ir())
        } else {
            matches!(subject, Fact::AtomicFact(AtomicFact::NotInFact(p))
                if p.element.ir() == fact.element.ir() && p.set.ir() == set.left.ir())
        };
        if !matches {
            return Err(LeanCompileError::unsupported("SetMinus/NegativePremise"));
        }
        let child = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let set = self.compile_object_reference(&fact.set, &complete)?;
        let element = self.compile_object_reference(&fact.element, &complete)?;
        let law = if right {
            "notInSetMinusOfRight"
        } else {
            "notInSetMinusOfLeft"
        };
        Ok(format!(
            "(let _set := {set}; Litex.{law} {element} _set.val.left _set.val.right {child})"
        ))
    }

    pub(super) fn compile_set_minus_subset_left(
        &self,
        fact: &SubsetFact,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::SetMinus(set)) = &fact.left else {
            return Err(LeanCompileError::unsupported("SetMinus/SubsetCarrier"));
        };
        if set.left.ir() != fact.right.ir() {
            return Err(LeanCompileError::unsupported("SetMinus/SubsetTarget"));
        }
        let set = self.compile_object_reference(&fact.left, position)?;
        Ok(format!(
            "(let _set := {set}; Litex.setMinusSubsetLeft _set.val.left _set.val.right)"
        ))
    }
}
