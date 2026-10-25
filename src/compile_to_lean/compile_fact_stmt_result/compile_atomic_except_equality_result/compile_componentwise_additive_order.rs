use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_componentwise_additive_order(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (crossed, strengths, law, requirements, results) = match strategy {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseLessEqual(p) => (
                false,
                [false, false],
                "addLeAdd",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddCrossedLessEqual(p) => (
                true,
                [false, false],
                "addLeAddSwap",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictLeft(p) => {
                (
                    false,
                    [true, false],
                    "addLtAddOfLtOfLe",
                    &p.requirement_facts,
                    &p.proof_of_requirement_facts,
                )
            }
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddComponentwiseStrictRight(
                p,
            ) => (
                false,
                [false, true],
                "addLtAddOfLeOfLt",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("ComponentwiseAdd/Strategy")),
        };
        let (low, high, strict) = source_order_oriented(goal)?;
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Add(left)),
            Obj::ArithmeticOperator(ArithmeticOperator::Add(right)),
        ) = (low, high)
        else {
            return Err(LeanCompileError::unsupported("ComponentwiseAdd/Sums"));
        };
        if strict != (strengths[0] || strengths[1]) || requirements.len() != 2 || results.len() != 2
        {
            return Err(LeanCompileError::unsupported(
                "ComponentwiseAdd/Requirements",
            ));
        }
        let lower = [left.left.as_ref(), left.right.as_ref()];
        let upper = if crossed {
            [right.right.as_ref(), right.left.as_ref()]
        } else {
            [right.left.as_ref(), right.right.as_ref()]
        };
        let mut children = Vec::new();
        for (i, (requirement, result)) in requirements.iter().zip(results).enumerate() {
            let Fact::AtomicFact(atomic) = requirement else {
                return Err(LeanCompileError::unsupported(
                    "ComponentwiseAdd/ChildFamily",
                ));
            };
            let (a, b, child_strict) = source_order_oriented(atomic)?;
            if child_strict != strengths[i]
                || a.ir() != lower[i].ir()
                || b.ir() != upper[i].ir()
                || source_subject(result)? != *requirement
            {
                return Err(LeanCompileError::new(
                    "ComponentwiseAdd/ChildSubject",
                    "The selected sum rule requires both original ordered operands, comparison strengths and matching child results.",
                ));
            }
            children.push(
                self.compile_verify(result, &position.atomic_search_prior(i)?)?
                    .1,
            );
        }
        let complete = position.atomic_search_prior(2)?;
        Ok(format!(
            "(Litex.{law} {} {} {} {})",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?,
            children[0],
            children[1],
        ))
    }
}
