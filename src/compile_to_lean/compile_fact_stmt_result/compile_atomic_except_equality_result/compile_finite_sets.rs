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
