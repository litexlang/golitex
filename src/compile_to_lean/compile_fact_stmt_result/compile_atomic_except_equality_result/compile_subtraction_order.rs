use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(super) fn compile_shared_subtraction_order(
        &self,
        goal: &AtomicFact,
        strategy: &AtomicExceptEqualityFactSearchProofByBuiltinStrategy,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let (common_left, strict, law, requirements, results) = match strategy {
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLessEqual(
                p,
            ) => (
                false,
                false,
                "subStructuralLeRight",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLessEqual(p) => (
                true,
                false,
                "subStructuralLeLeft",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedSubtrahendLess(p) => (
                false,
                true,
                "subStructuralLtRight",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            AtomicExceptEqualityFactSearchProofByBuiltinStrategy::SubSharedMinuendLess(p) => (
                true,
                true,
                "subStructuralLtLeft",
                &p.requirement_facts,
                &p.proof_of_requirement_facts,
            ),
            _ => return Err(LeanCompileError::unsupported("SharedSubtraction/Strategy")),
        };
        let (low, high, goal_strict) = source_order_oriented(goal)?;
        let (
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(lhs)),
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(rhs)),
        ) = (low, high)
        else {
            return Err(LeanCompileError::unsupported(
                "SharedSubtraction/Differences",
            ));
        };
        if goal_strict != strict || requirements.len() != 1 || results.len() != 1 {
            return Err(LeanCompileError::unsupported(
                "SharedSubtraction/Requirements",
            ));
        }
        let (common, other_common, a, b, field) = if common_left {
            (&lhs.left, &rhs.left, &rhs.right, &lhs.right, "left")
        } else {
            (&lhs.right, &rhs.right, &lhs.left, &rhs.left, "right")
        };
        if common.ir() != other_common.ir() {
            return Err(LeanCompileError::unsupported(
                "SharedSubtraction/CommonOperand",
            ));
        }
        let Fact::AtomicFact(requirement) = &requirements[0] else {
            return Err(LeanCompileError::unsupported(
                "SharedSubtraction/ChildFamily",
            ));
        };
        let (child_low, child_high, child_strict) = source_order_oriented(requirement)?;
        if child_strict != strict
            || child_low.ir() != a.ir()
            || child_high.ir() != b.ir()
            || source_subject(&results[0])? != requirements[0]
        {
            return Err(LeanCompileError::new(
                "SharedSubtraction/ChildSubject",
                "The selected subtraction rule requires the original operand order, comparison strength and matching child result.",
            ));
        }
        let order = self
            .compile_verify(&results[0], &position.atomic_search_prior(0)?)?
            .1;
        let complete = position.atomic_search_prior(1)?;
        let real = self.compile_real_membership_certificate(low, &complete)?;
        Ok(format!(
            "(by\n  let _litex_sub_left := {}\n  let _litex_sub_right := {}\n  exact Litex.{law} _litex_sub_left _litex_sub_right {real} {order} (Litex.sameRefl _litex_sub_left.val.{field})\n)",
            self.compile_object_reference(low, &complete)?,
            self.compile_object_reference(high, &complete)?,
        ))
    }
}
