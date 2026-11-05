use crate::compile_to_lean::helper::source_subject;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError,LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::IntersectFiniteFromBothStrategySingleStep;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_strategy::result::{IntersectFiniteFromLeftStrategySingleStep, IntersectFiniteFromRightStrategySingleStep};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_intersection_from_left(
        &self,
        fact: &AtomicFact,
        proof: &IntersectFiniteFromLeftStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_finite_intersection_one_bound(
            fact,
            &proof.requirement_facts,
            &proof.proof_of_requirement_facts,
            true,
            position,
        )
    }

    pub(in crate::compile_to_lean) fn compile_finite_intersection_from_right(
        &self,
        fact: &AtomicFact,
        proof: &IntersectFiniteFromRightStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        self.compile_finite_intersection_one_bound(
            fact,
            &proof.requirement_facts,
            &proof.proof_of_requirement_facts,
            false,
            position,
        )
    }

    fn compile_finite_intersection_one_bound(
        &self,
        fact: &AtomicFact,
        requirements: &[Fact],
        results: &[VerifyFactResult],
        from_left: bool,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsFiniteSetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported(
                "FiniteIntersectionOneBound/Subject",
            ));
        };
        let Obj::SetOperator(SetOperator::Intersect(pair)) = &fact.set else {
            return Err(LeanCompileError::unsupported(
                "FiniteIntersectionOneBound/Set",
            ));
        };
        if requirements.len() != 1 || results.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "FiniteIntersectionOneBound/Stages",
            ));
        }
        let operand = if from_left { &pair.left } else { &pair.right };
        if !matches!(&requirements[0], Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir() == operand.ir())
            || source_subject(&results[0])? != requirements[0]
        {
            return Err(LeanCompileError::unsupported(
                "FiniteIntersectionOneBound/Premise",
            ));
        }
        let premise = self
            .compile_verify(&results[0], &position.atomic_search_prior(0)?)?
            .1;
        let set = self.compile_object_reference(&fact.set, &position.atomic_search_prior(1)?)?;
        let bridge = if from_left {
            "finiteSetIntersectFromLeft"
        } else {
            "finiteSetIntersectFromRight"
        };
        Ok(format!("(Litex.{bridge} {set} {premise})"))
    }

    pub(in crate::compile_to_lean) fn compile_finite_intersection(
        &self,
        fact: &AtomicFact,
        proof: &IntersectFiniteFromBothStrategySingleStep,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsFiniteSetFact(fact) = fact else {
            return Err(LeanCompileError::unsupported("FiniteIntersection/Subject"));
        };
        let Obj::SetOperator(SetOperator::Intersect(pair)) = &fact.set else {
            return Err(LeanCompileError::unsupported("FiniteIntersection/Set"));
        };
        if proof.requirement_facts.len() != 2 || proof.proof_of_requirement_facts.len() != 2 {
            return Err(LeanCompileError::unsupported("FiniteIntersection/Stages"));
        }
        let mut checked = Vec::new();
        for (index, set) in [&pair.left, &pair.right].iter().enumerate() {
            let requirement = &proof.requirement_facts[index];
            let result = &proof.proof_of_requirement_facts[index];
            if !matches!(requirement,Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir()==set.ir())
                || source_subject(result)? != *requirement
            {
                return Err(LeanCompileError::unsupported("FiniteIntersection/Premise"));
            }
            checked.push(
                self.compile_verify(result, &position.atomic_search_prior(index)?)?
                    .1,
            );
        }
        let set = self.compile_object_reference(&fact.set, &position.atomic_search_prior(2)?)?;
        Ok(format!(
            "(Litex.finiteSetIntersect {set} {} {})",
            checked[0], checked[1]
        ))
    }
}

impl LitexToLeanCompiler {
    pub(super) fn compile_finite_function_range(
        &self,
        goal: &IsFiniteSetFact,
        proof: &crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::is_finite_set::FunctionRangeOfFiniteDomainProof,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let Obj::FunctionSpace(FunctionSpace::FnRange(range)) = &goal.set else {
            return Err(LeanCompileError::unsupported(
                "FiniteFunctionRange/Constructor",
            ));
        };
        let membership = source_subject(&proof.function_membership)?;
        let Fact::AtomicFact(AtomicFact::InFact(member)) = &membership else {
            return Err(LeanCompileError::unsupported(
                "FiniteFunctionRange/Membership",
            ));
        };
        let Obj::FunctionSpace(FunctionSpace::FnSet(signature)) = &member.set else {
            return Err(LeanCompileError::unsupported(
                "FiniteFunctionRange/Signature",
            ));
        };
        let groups: Vec<_> = signature
            .set_bound_parameters
            .groups
            .iter()
            .filter(|g| !g.params.is_empty())
            .collect();
        if member.element.ir() != range.function.ir()
            || groups.len() != 1
            || groups[0].params.len() != 1
        {
            return Err(LeanCompileError::unsupported(
                "FiniteFunctionRange/UnarySubject",
            ));
        }
        let domain = groups[0].param_type.as_ref();
        if !matches!(source_subject(&proof.domain_finite)?,Fact::AtomicFact(AtomicFact::IsFiniteSetFact(p)) if p.set.ir()==domain.ir())
        {
            return Err(LeanCompileError::unsupported(
                "FiniteFunctionRange/FiniteSubject",
            ));
        }
        let finite =
            self.compile_verify(&proof.domain_finite, &position.atomic_search_prior(0)?)?;
        let member = self.compile_verify(
            &proof.function_membership,
            &position.atomic_search_prior(1)?,
        )?;
        let formed = position.atomic_search_prior(2)?;
        let range = self.compile_object_reference(&goal.set, &formed)?;
        let domain = self.compile_object_reference(domain, &formed)?;
        let signature_term = self.compile_fn_signature(signature, &formed)?;
        let (mut lines, _, _) =
            self.compile_preimage_domain_parts(signature, "_range_input", &formed)?;
        lines.insert(0, "intro _range_input _preimage_domain".into());
        lines.push("exact _preimage_base".into());
        Ok(format!("(by\n  have _finite_domain : {} := {}\n  have _finite_function : {} := {}\n  exact Litex.fnRangeFiniteOfFiniteCover {range} {signature_term} {domain} _finite_function _finite_domain (by\n    {}\n  )\n)", finite.0, finite.1.replace('\n',"\n  "),member.0,member.1.replace('\n',"\n  "),lines.join("\n").replace('\n',"\n    ")))
    }
}
