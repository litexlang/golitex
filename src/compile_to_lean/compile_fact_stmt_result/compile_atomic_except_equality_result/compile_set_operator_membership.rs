use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::in_fact::{
    InFactSearchProofByBuiltinRule, PowerSetMembershipSubsetProof,
};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::PowerSetMembershipStrategySingleStep;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_sym_diff_membership(
        &self,
        goal: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        expected: [bool; 2],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (element, set, positive) = match goal {
            AtomicFact::InFact(p) => (&p.element, &p.set, true),
            AtomicFact::NotInFact(p) => (&p.element, &p.set, false),
            _ => return Err(LeanCompileError::unsupported("SymDiff/MemberFamily")),
        };
        let Obj::SetOperator(SetOperator::SymmetricDifference(pair)) = set else {
            return Err(LeanCompileError::unsupported("SymDiff/MemberObject"));
        };
        if positive != (expected[0] != expected[1]) || requirements.len() != 2 || proofs.len() != 2
        {
            return Err(LeanCompileError::unsupported("SymDiff/MemberStages"));
        }
        let mut compiled = Vec::new();
        for (i, (child, want)) in [pair.left.as_ref(), pair.right.as_ref()]
            .into_iter()
            .zip(expected)
            .enumerate()
        {
            let subject = match &requirements[i] {
                Fact::AtomicFact(AtomicFact::InFact(p)) if want => Some((&p.element, &p.set)),
                Fact::AtomicFact(AtomicFact::NotInFact(p)) if !want => Some((&p.element, &p.set)),
                _ => None,
            };
            if !subject.is_some_and(|(x, a)| x.ir() == element.ir() && a.ir() == child.ir())
                || source_subject(&proofs[i])? != requirements[i]
            {
                return Err(LeanCompileError::unsupported("SymDiff/MemberPremise"));
            }
            compiled.push(
                self.compile_verify(&proofs[i], &position.atomic_search_prior(i)?)?
                    .1,
            );
        }
        let law = match expected {
            [true, false] => "inSymmetricDifferenceLeft",
            [false, true] => "inSymmetricDifferenceRight",
            [true, true] => "notInSymmetricDifferenceBoth",
            [false, false] => "notInSymmetricDifferenceNeither",
        };
        let complete = position.atomic_search_prior(2)?;
        Ok(format!(
            "(Litex.{law} {} {} {} {})",
            self.compile_object_reference(element, &complete)?,
            self.compile_object_reference(set, &complete)?,
            compiled[0],
            compiled[1]
        ))
    }

    pub(in crate::compile_to_lean) fn compile_power_set_membership_strategy(
        &self,
        fact: &InFact,
        proof: &PowerSetMembershipStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::SetOperator(SetOperator::PowerSet(power)) = &fact.set else {
            return Err(LeanCompileError::new(
                "PowerSet/StrategySubject",
                "The selected power-set strategy has another set constructor.",
            ));
        };
        let ([requirement], [child]) = (
            proof.requirement_facts.as_slice(),
            proof.proof_of_requirement_facts.as_slice(),
        ) else {
            return Err(LeanCompileError::new(
                "PowerSet/StrategyRequirements",
                "Power-set membership requires its one original subset premise.",
            ));
        };
        if !matches!(requirement, Fact::AtomicFact(AtomicFact::SubsetFact(subset))
            if subset.left.ir() == fact.element.ir() && subset.right.ir() == power.set.ir())
            || source_subject(child)? != *requirement
        {
            return Err(LeanCompileError::new(
                "PowerSet/StrategySubsetSubject",
                "The recorded premise or proof has another member or power-set base.",
            ));
        }
        let certificate = self
            .compile_verify(child, &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        Ok(format!(
            "((Litex.inPowerSet_iff {} {}).mpr {certificate})",
            self.compile_object_reference(&fact.element, &complete)?,
            self.compile_object_reference(&power.set, &complete)?
        ))
    }

    pub(in crate::compile_to_lean) fn compile_set_operator_membership(
        &self,
        fact: &InFact,
        rule: &InFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        match (rule, &fact.set) {
            (InFactSearchProofByBuiltinRule::SetMinusMembership(p), _) => self
                .compile_set_minus_membership(
                    fact,
                    [&p.left_membership_proof, &p.right_non_membership_proof],
                    position,
                ),
            (InFactSearchProofByBuiltinRule::IntersectMembership(proof), _) => self
                .compile_intersection_membership(
                    fact,
                    [&proof.left_membership_proof, &proof.right_membership_proof],
                    position,
                ),
            (
                InFactSearchProofByBuiltinRule::PowerSetMembership(proof),
                Obj::SetOperator(SetOperator::PowerSet(power)),
            ) => {
                let (subject, certificate) = match &proof.subset_proof {
                    PowerSetMembershipSubsetProof::KnownSubset(known) => {
                        let AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(citation) =
                            known.searched_proof.as_ref()
                        else {
                            return Err(LeanCompileError::unsupported("PowerSet/KnownSubsetRoute"));
                        };
                        (
                            &known.fact,
                            self.compile_known_atomic(citation, &known.fact, position)?,
                        )
                    }
                    PowerSetMembershipSubsetProof::VerifiedSubset(verified) => (
                        &verified.fact,
                        self.compile_verify_atomic_success(
                            verified,
                            &position.atomic_search_prior(0)?,
                        )?
                        .1,
                    ),
                };
                if !matches!(subject, AtomicFact::SubsetFact(subset) if subset.left.ir() == fact.element.ir() && subset.right.ir() == power.set.ir())
                {
                    return Err(LeanCompileError::new(
                        "PowerSet/SubsetSubject",
                        "The captured subset has another member or power-set base.",
                    ));
                }
                Ok(format!(
                    "((Litex.inPowerSet_iff {} {}).mpr {certificate})",
                    self.compile_object_reference(&fact.element, position)?,
                    self.compile_object_reference(&power.set, position)?
                ))
            }
            (
                InFactSearchProofByBuiltinRule::UnionMembershipFromLeft(proof),
                Obj::SetOperator(SetOperator::Union(union)),
            ) => self.compile_union_membership(
                fact,
                union,
                &proof.left_membership_proof,
                true,
                position,
            ),
            (
                InFactSearchProofByBuiltinRule::UnionMembershipFromRight(proof),
                Obj::SetOperator(SetOperator::Union(union)),
            ) => self.compile_union_membership(
                fact,
                union,
                &proof.right_membership_proof,
                false,
                position,
            ),
            _ => Err(LeanCompileError::new(
                "SetOperator/MembershipSubject",
                "The membership rule has another set constructor.",
            )),
        }
    }

    pub(super) fn compile_union_membership_strategy(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        proofs: &[VerifyFactResult],
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::InFact(member) = fact else {
            return Err(LeanCompileError::unsupported("Union/StrategyFamily"));
        };
        let Obj::SetOperator(SetOperator::Union(union)) = &member.set else {
            return Err(LeanCompileError::unsupported("Union/StrategyCarrier"));
        };
        let ([requirement], [proof]) = (requirements, proofs) else {
            return Err(LeanCompileError::unsupported("Union/StrategyStages"));
        };
        if source_subject(proof)? != *requirement {
            return Err(LeanCompileError::unsupported("Union/StrategyRequirement"));
        }
        self.compile_union_membership(member, union, proof, left, position)
    }

    fn compile_union_membership(
        &self,
        fact: &InFact,
        union: &Union,
        proof: &VerifyFactResult,
        left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let factor = if left { &union.left } else { &union.right };
        if !matches!(source_subject(proof)?, Fact::AtomicFact(AtomicFact::InFact(member)) if member.element.ir() == fact.element.ir() && member.set.ir() == factor.ir())
        {
            return Err(LeanCompileError::new(
                "Union/MemberSubject",
                "The recorded membership has another element or selected factor.",
            ));
        }
        let certificate = self
            .compile_verify(proof, &position.atomic_search_prior(0)?)?
            .1;
        let injection = if left { "Or.inl" } else { "Or.inr" };
        Ok(format!(
            "((Litex.inUnion_iff {} {} {}).mpr ({injection} {certificate}))",
            self.compile_object_reference(&fact.element, position)?,
            self.compile_object_reference(&union.left, position)?,
            self.compile_object_reference(&union.right, position)?
        ))
    }
}
