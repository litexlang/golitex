use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::{SourceOwner, SourcePosition};
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::ExistShapedFactSearchProofByBuiltinRule;
use crate::prelude::*;
use std::collections::HashSet;

impl LitexToLeanCompiler {
    pub(super) fn compile_exist_builtin_result(
        &self,
        fact: &PlainExistFact,
        proof: &ExistShapedFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match proof {
            ExistShapedFactSearchProofByBuiltinRule::RealLineComparisonWitness(proof) => self
                .compile_exist_real_equality_witness(
                    fact,
                    &proof.requirement_facts,
                    &proof.proof_of_requirement_facts,
                    position,
                ),
            _ => Err(LeanCompileError::unsupported("Exist/BuiltinRule")),
        }
    }

    // Replay the selected rule's one-real equality case. The source verifier
    // selects this before its general membership-witness rule or known-exist
    // lookup; neither later route can replace this retained membership child.
    fn compile_exist_real_equality_witness(
        &self,
        fact: &PlainExistFact,
        requirements: &[Fact],
        children: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let [group] = fact.typed_parameters.groups.as_slice() else {
            return Err(LeanCompileError::unsupported("Exist/RealLineEqualityShape"));
        };
        let [parameter] = group.params.as_slice() else {
            return Err(LeanCompileError::unsupported("Exist/RealLineEqualityShape"));
        };
        let (
            ParamType::Obj(Obj::StandardSet(StandardSet::R)),
            [QuantifierFreeFact::AtomicFact(AtomicFact::EqualFact(equality))],
        ) = (&group.param_type, fact.facts.as_slice())
        else {
            return Err(LeanCompileError::unsupported("Exist/RealLineEqualityShape"));
        };
        let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
        let operand = if equality.left.ir() == bound.ir() {
            &equality.right
        } else if equality.right.ir() == bound.ir() {
            &equality.left
        } else {
            return Err(LeanCompileError::new(
                "Exist/RealLineEqualitySubject",
                "The original equality does not use its existential parameter as an endpoint.",
            ));
        };
        let mut free = HashSet::new();
        crate::instantiate::collect_free_plain_ids(operand, &HashSet::new(), &mut free);
        if free.contains(&parameter.id) {
            return Err(LeanCompileError::new(
                "Exist/RealLineEqualitySubject",
                "The selected free endpoint depends on the existential parameter.",
            ));
        }
        let ([requirement], [child]) = (requirements, children) else {
            return Err(LeanCompileError::new(
                "Exist/RealLineEqualityRequirements",
                "The selected one-real witness requires its one ordered membership and verification.",
            ));
        };
        if !matches!(requirement,
            Fact::AtomicFact(AtomicFact::InFact(member))
                if member.element.ir() == operand.ir()
                    && matches!(member.set, Obj::StandardSet(StandardSet::R)))
        {
            return Err(LeanCompileError::new(
                "Exist/RealLineEqualityMembership",
                "The original requirement is not membership of this free endpoint in R.",
            ));
        }
        let checked = source_subject(child)?;
        if checked != *requirement || checked.fact_id() != requirement.fact_id() {
            return Err(LeanCompileError::new(
                "Exist/RealLineEqualityChild",
                "The selected child does not prove the exact original membership requirement.",
            ));
        }
        let membership = self.compile_verify(child, position)?;
        let complete = SourcePosition::new(Some(position), SourceOwner::Verify(child), usize::MAX);
        let value = self.compile_object_reference(operand, &complete)?;
        Ok(format!(
            "⟨Litex.semanticObject (Litex.denote {value}) (Litex.isSet {value}), {}, (by rfl)⟩",
            membership.1,
        ))
    }
}
