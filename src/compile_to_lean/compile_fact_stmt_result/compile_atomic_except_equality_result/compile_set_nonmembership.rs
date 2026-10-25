use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_intersection_nonmembership(
        &self,
        fact: &NotInFact,
        proof: &VerifyFactResult,
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Intersect(set)) = &fact.set else {
            return Err(LeanCompileError::unsupported("NotInIntersect/Carrier"));
        };
        let bound = if left { &set.left } else { &set.right };
        if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::NotInFact(p))
            if p.element.ir() == fact.element.ir() && p.set.ir() == bound.ir())
        {
            return Err(LeanCompileError::unsupported("NotInIntersect/Premise"));
        }
        let child = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let set = self.compile_object_reference(&fact.set, &complete)?;
        let element = self.compile_object_reference(&fact.element, &complete)?;
        let law = if left {
            "notInIntersectOfLeft"
        } else {
            "notInIntersectOfRight"
        };
        Ok(format!(
            "(let _set := {set}; Litex.{law} {element} _set.val.left _set.val.right {child})"
        ))
    }

    pub(super) fn compile_union_nonmembership(
        &self,
        fact: &NotInFact,
        proofs: [&VerifyFactResult; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::Union(set)) = &fact.set else {
            return Err(LeanCompileError::unsupported("NotInUnion/Carrier"));
        };
        let mut children = Vec::new();
        for (index, (proof, bound)) in proofs.into_iter().zip([&set.left, &set.right]).enumerate() {
            if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::NotInFact(p))
                if p.element.ir() == fact.element.ir() && p.set.ir() == bound.ir())
            {
                return Err(LeanCompileError::unsupported("NotInUnion/Premise"));
            }
            children.push(
                self.compile_verify(proof, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        let set = self.compile_object_reference(&fact.set, &complete)?;
        let element = self.compile_object_reference(&fact.element, &complete)?;
        Ok(format!(
            "(let _set := {set}; Litex.notInUnion {element} _set.val.left _set.val.right {} {})",
            children[0], children[1]
        ))
    }
}
