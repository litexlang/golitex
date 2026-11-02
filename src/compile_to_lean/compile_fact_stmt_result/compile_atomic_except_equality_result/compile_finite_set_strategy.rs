use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_finite_union_or_difference(
        &self,
        goal: &AtomicFact,
        union: bool,
        requirements: &[Fact],
        results: &[VerifyFactResult],
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::IsFiniteSetFact(fact) = goal else {
            return Err(LeanCompileError::unsupported(
                "FiniteSetConstructor/Subject",
            ));
        };
        let (a, b, law) = match (&fact.set, union) {
            (Obj::SetOperator(SetOperator::Union(p)), true) => {
                (&p.left, &p.right, "finiteUnionFromBoth")
            }
            (Obj::SetOperator(SetOperator::SetMinus(p)), false) => {
                (&p.left, &p.right, "finiteDifferenceFromLeft")
            }
            _ => {
                return Err(LeanCompileError::unsupported(
                    "FiniteSetConstructor/Operator",
                ))
            }
        };
        let count = if union { 2 } else { 1 };
        if requirements.len() != count || results.len() != count {
            return Err(LeanCompileError::unsupported("FiniteSetConstructor/Stages"));
        }
        let mut definitions = Vec::new();
        for (index, ((requirement, result), operand)) in
            requirements.iter().zip(results).zip([a, b]).enumerate()
        {
            if !matches!(requirement,Fact::AtomicFact(AtomicFact::IsFiniteSetFact(f)) if f.set.ir()==operand.ir())
                || source_subject(result)? != *requirement
            {
                return Err(LeanCompileError::unsupported(
                    "FiniteSetConstructor/Premise",
                ));
            }
            let prior = position.atomic_search_prior(index)?;
            let compiled = self.compile_verify(result, &prior)?;
            definitions.push(self.emit_internal_fact(requirement, &compiled, &prior)?);
        }
        let complete = position.atomic_search_prior(count)?;
        let set = self.compile_object_reference(&fact.set, &complete)?;
        let arguments = requirements
            .iter()
            .map(|r| format!("h_{}", r.fact_id().value()))
            .collect::<Vec<_>>()
            .join(" ");
        Ok(format!("(by\n  {}\n  let _finite_set := {set}\n  exact Litex.{law} _finite_set.val.left _finite_set.val.right {arguments}\n)",definitions.join("\n").replace('\n',"\n  ")))
    }
}
