use crate::compile_to_lean::helper::*;
use crate::compile_to_lean::source_position::SourcePosition;
use crate::compile_to_lean::{LeanCompileError, LitexToLeanCompiler};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::search_atomic_except_equality_fact_proof_by_builtin_rules::less_equal::LessEqualFactSearchProofByBuiltinRule;
use crate::prelude::*;

impl LitexToLeanCompiler {
    pub(in crate::compile_to_lean) fn compile_nonnegative_builtin(
        &self,
        goal: &AtomicFact,
        rule: &LessEqualFactSearchProofByBuiltinRule,
        position: &SourcePosition<'_>,
    ) -> Result<String, LeanCompileError> {
        let AtomicFact::LessEqualFact(goal) = goal else {
            return Err(LeanCompileError::new(
                "NonnegativeBuiltin/GoalFamily",
                "The selected builtin must retain its weak less-equal conclusion.",
            ));
        };
        if !is_exact_zero(&goal.left) {
            return Err(LeanCompileError::new(
                "NonnegativeBuiltin/ZeroBound",
                "The selected sum or product must retain its exact lower bound zero.",
            ));
        }
        let (law, operands, children) = match (&goal.right, rule) {
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Add(sum)),
                LessEqualFactSearchProofByBuiltinRule::SumOfNonnegatives(proof),
            ) => (
                "addNonnegative",
                [sum.left.as_ref(), sum.right.as_ref()],
                [
                    &proof.left_nonnegative_proof,
                    &proof.right_nonnegative_proof,
                ],
            ),
            (
                Obj::ArithmeticOperator(ArithmeticOperator::Mul(product)),
                LessEqualFactSearchProofByBuiltinRule::ProductOfNonnegatives(proof),
            ) => (
                "mulNonnegative",
                [product.left.as_ref(), product.right.as_ref()],
                [
                    &proof.left_nonnegative_proof,
                    &proof.right_nonnegative_proof,
                ],
            ),
            _ => {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/Constructor",
                    "The selected builtin must retain its own sum or product constructor.",
                ))
            }
        };
        let mut proofs = Vec::new();
        for (index, (child, operand)) in children.into_iter().zip(operands).enumerate() {
            let subject = source_subject(child)?;
            let Fact::AtomicFact(atomic) = &subject else {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/ChildFamily",
                    "The original nonnegative premise must be an atomic order fact.",
                ));
            };
            let (zero, value, strict) = source_order_oriented(atomic)?;
            if !is_exact_zero(zero) || value.ir() != operand.ir() {
                return Err(LeanCompileError::new(
                    "NonnegativeBuiltin/ChildSubject",
                    "The ordered child must certify the same operand's lower bound zero.",
                ));
            }
            let prior = position.atomic_search_prior(index)?;
            let proof = self.compile_verify(child, &prior)?.1;
            let side = if index == 0 { "left" } else { "right" };
            // The producer may retain a strict positive premise unchanged.
            // Its actual proof is replayed before weakening its conclusion.
            proofs.push(if strict {
                format!("(Litex.ltToLe (Litex.number (M := M) 0) _litex_nonnegative.val.{side} {proof})")
            } else {
                proof
            });
        }
        let formed = position.atomic_search_prior(0)?;
        let term = self.compile_object_reference(&goal.right, &formed)?;
        Ok(format!(
            "(by\n  let _litex_nonnegative := {term}\n  exact Litex.{law} _litex_nonnegative.val.left _litex_nonnegative.val.right _litex_nonnegative.wd.1 _litex_nonnegative.wd.2 {} {}\n)",
            proofs[0], proofs[1],
        ))
    }
}
