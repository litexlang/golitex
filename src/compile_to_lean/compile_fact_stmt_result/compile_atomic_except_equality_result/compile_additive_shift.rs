use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_weak_additive_shift(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        // The recorded variant selects the law and operand orientation. The
        // goal is checked against that selection; it never chooses a proof.
        let (sum_on_right, bound_on_left, law, requirements, results) = match strategy {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftLeft(
                p,
            ) => (
                true,
                true,
                "leAddOfLeOfNonneg",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddRightNonnegativeShiftRight(
                p,
            ) => (
                true,
                false,
                "leAddOfLeOfNonnegSwap",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftLeft(
                p,
            ) => (
                false,
                true,
                "addLeOfLeOfNonpos",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::AddLeftNonpositiveShiftRight(
                p,
            ) => (
                false,
                false,
                "addLeOfLeOfNonposSwap",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("WeakAddShift/Strategy")),
        };
        let (low, high, strict) = source_order_oriented(goal)?;
        let sum = if sum_on_right { high } else { low };
        let Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)) = sum else {
            return Err(LeanCompileError::unsupported("WeakAddShift/Sum"));
        };
        if strict || requirements.len() != 2 || results.len() != 2 {
            return Err(LeanCompileError::unsupported("WeakAddShift/Requirements"));
        }
        let (bounded, signed) = if bound_on_left {
            (sum.left.as_ref(), sum.right.as_ref())
        } else {
            (sum.right.as_ref(), sum.left.as_ref())
        };
        let mut children = Vec::new();
        for (i, (requirement, result)) in requirements.iter().zip(results).enumerate() {
            let Fact::AtomicFact(atomic) = requirement else {
                return Err(LeanCompileError::unsupported("WeakAddShift/ChildFamily"));
            };
            let (left, right, strict) = source_order_oriented(atomic)?;
            let subject_matches = match (sum_on_right, i) {
                (true, 0) => left.ir() == low.ir() && right.ir() == bounded.ir(),
                (false, 0) => left.ir() == bounded.ir() && right.ir() == high.ir(),
                (true, 1) => is_exact_zero(left) && right.ir() == signed.ir(),
                (false, 1) => left.ir() == signed.ir() && is_exact_zero(right),
                _ => unreachable!(),
            };
            if strict || !subject_matches || source_subject(result)? != *requirement {
                return Err(LeanCompileError::new(
                    "WeakAddShift/ChildSubject",
                    "The selected shift requires the original bound followed by the signed addend, with exact subjects and weak comparisons.",
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
